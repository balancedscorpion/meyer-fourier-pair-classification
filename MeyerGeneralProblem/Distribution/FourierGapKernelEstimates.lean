module

public import MeyerGeneralProblem.Distribution.FourierGapPrimitives
public import MeyerGeneralProblem.Distribution.CompactSchwartzDensity
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Weighted estimates for the Fourier-gap primitive kernels

Exact inverse power tails of the frequency multiplier give integrable
frequency derivatives of every order. Fourier differentiation transfers
these bounds to polynomial weights on the physical kernel.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff FourierTransform Topology

private theorem inv_abs_pow_le_inv_quadratic {x : ℝ} (hx : 1 ≤ |x|)
    {p : ℕ} (hp : 2 ≤ p) : (|x| ^ p)⁻¹ ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have hx0 : 0 < |x| := zero_lt_one.trans_le hx
  have hPow : |x| ^ 2 ≤ |x| ^ p := pow_le_pow_right₀ hx hp
  have hOne := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hx 2
  rw [one_pow, sq_abs] at hOne
  have hDiv : 1 / |x| ^ 2 ≤ 2 / (1 + x ^ 2) :=
    (div_le_div_iff₀ (pow_pos hx0 2) (by positivity)).mpr (by rw [one_mul, sq_abs]; linarith)
  exact ((inv_le_inv₀ (pow_pos hx0 _) (pow_pos hx0 _)).mpr hPow).trans
    (by simpa only [div_eq_mul_inv, one_mul] using hDiv)

private theorem integrable_iteratedDeriv_of_inverse_power_tails
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (r : ℝ) (c : ℂ) (p : ℕ) (hp : 2 ≤ p)
    (hTail : ∀ x : ℝ, r ≤ |x| → f x = x ^ (-(p : ℤ)) • c) (k : ℕ) :
    Integrable (iteratedDeriv k f) := by
  let s := max 1 r
  let b : ℝ := ∏ i ∈ Finset.range k, (((-(p : ℤ) : ℤ) : ℝ) - (i : ℝ))
  have hCont : Continuous (iteratedDeriv k f) :=
    hf.continuous_iteratedDeriv k (by simp)
  have hLocal : IntegrableOn (iteratedDeriv k f) (closedBall (0 : ℝ) s) :=
    hCont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hFar : IntegrableOn (iteratedDeriv k f) (closedBall (0 : ℝ) s)ᶜ := by
    apply (integrable_inv_one_add_sq.const_mul (2 * (|b| * ‖c‖))).integrableOn.mono'
      hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (isClosed_closedBall.measurableSet.compl)] with x hx
    have hxs : s < |x| := not_le.mp (by
      simpa only [mem_compl_iff, mem_closedBall, Real.dist_eq, sub_zero] using hx)
    have hx1 : 1 ≤ |x| := (le_max_left 1 r).trans hxs.le
    have hx0 : x ≠ 0 := abs_pos.mp (zero_lt_one.trans_le hx1)
    have hxr : r < |x| := (le_max_right 1 r).trans_lt hxs
    have heq : f =ᶠ[𝓝 x] fun y : ℝ => y ^ (-(p : ℤ)) • c := by
      have hOpen : IsOpen {y : ℝ | r < |y|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [hOpen.mem_nhds hxr] with y hy
      exact hTail y (show r < |y| from hy).le
    have hSmooth : ContDiffAt ℝ k (fun y : ℝ => y ^ (-(p : ℤ))) x := by
      simp only [zpow_neg, zpow_natCast]
      exact (contDiffAt_id.pow p).inv (pow_ne_zero p hx0)
    have hDeriv : iteratedDeriv k f x = (b * x ^ (-((p + k : ℕ) : ℤ))) • c := by
      rw [heq.iteratedDeriv_eq k, iteratedDeriv_smul_const hSmooth,
        iteratedDeriv_eq_iterate, iter_deriv_zpow]
      have hExponent : -(p : ℤ) - (k : ℤ) = -((p + k : ℕ) : ℤ) := by push_cast; ring
      rw [hExponent]
    rw [hDeriv, norm_smul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, zpow_neg, zpow_natCast,
      abs_inv, abs_pow]
    have h := inv_abs_pow_le_inv_quadratic hx1 (hp.trans (Nat.le_add_right p k))
    calc
      (|b| * (|x| ^ (p + k))⁻¹) * ‖c‖ ≤ (|b| * (2 * (1 + x ^ 2)⁻¹)) * ‖c‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (abs_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  simpa only [union_compl_self, integrableOn_univ] using hLocal.union hFar

private theorem integrable_iteratedDeriv_fourier_primitive_moment
    (a : ℝ → ℂ) (ha : a.HasTemperateGrowth) (r : ℝ)
    (hRecip : ∀ x : ℝ, r ≤ |x| →
      a x = ((2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ))⁻¹)
    (j m : ℕ) (hm : j + 2 ≤ m) (k : ℕ) :
    Integrable (iteratedDeriv k
      (fun x : ℝ => ((2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)) ^ j * a x ^ m)) := by
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  let p := m - j
  have hp : 2 ≤ p := by dsimp [p]; omega
  have hd : ContDiff ℝ ∞ (fun x : ℝ => c * (x : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  apply integrable_iteratedDeriv_of_inverse_power_tails _ ((hd.pow j).mul (ha.1.pow m))
    (max 1 r) (c ^ p)⁻¹ p hp _ k
  intro x hx
  have hx0 : x ≠ 0 := abs_pos.mp
    (zero_lt_one.trans_le ((le_max_left 1 r).trans hx))
  let u : ℂ := c * (x : ℂ)
  have hu : u ≠ 0 := mul_ne_zero hc (Complex.ofReal_ne_zero.mpr hx0)
  rw [hRecip x ((le_max_right 1 r).trans hx)]
  change u ^ j * u⁻¹ ^ m = x ^ (-(p : ℤ)) • (c ^ p)⁻¹
  have hSplit : u ^ m = u ^ j * u ^ p := by
    rw [← pow_add, show j + p = m by dsimp [p]; omega]
  rw [inv_pow, hSplit, mul_inv_rev, mul_comm (u ^ p)⁻¹, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero j hu), one_mul]
  simp only [u, mul_pow, mul_inv_rev, zpow_neg, zpow_natCast, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_pow]

private theorem norm_inverseFourier_le_integral_norm (f : ℝ → ℂ) (x : ℝ) :
    ‖(𝓕⁻ f) x‖ ≤ ∫ t : ℝ, ‖f t‖ := by
  rw [Real.fourierInv_eq]
  exact (norm_integral_le_integral_norm _).trans (by simp only [Circle.norm_smul, le_refl])

private theorem norm_pow_mul_norm_inverseFourier_le
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hIntegrable : ∀ j : ℕ, Integrable (iteratedDeriv j f)) (k : ℕ) (x : ℝ) :
    |x| ^ k * ‖(𝓕⁻ f) x‖ ≤
      ‖2 * (Real.pi : ℂ) * Complex.I‖⁻¹ ^ k * ∫ t : ℝ, ‖iteratedDeriv k f t‖ := by
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hc : 0 < ‖c‖ := norm_pos_iff.mpr
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero)
  have hF := congrFun
    (Real.fourier_iteratedDeriv (n := k) (N := ⊤) (hf.of_le (by simp))
      (fun j _ => hIntegrable j) (by simp)) (-x)
  rw [← Real.fourierInv_eq_fourier_neg, ← Real.fourierInv_eq_fourier_neg] at hF
  have hBound := norm_inverseFourier_le_integral_norm (iteratedDeriv k f) x
  rw [hF, norm_smul, norm_pow] at hBound
  change ‖c * ((-x : ℝ) : ℂ)‖ ^ k * ‖(𝓕⁻ f) x‖ ≤ _ at hBound
  rw [norm_mul, Complex.norm_real, norm_neg, Real.norm_eq_abs, mul_pow, mul_assoc] at hBound
  change _ ≤ ‖c‖⁻¹ ^ k * _
  rw [inv_pow, ← div_eq_inv_mul]
  exact (le_div_iff₀ (pow_pos hc _)).mpr (by simpa only [mul_comm] using hBound)

/-- The kernel derivatives through order m minus two are uniformly
bounded with every nonnegative integral polynomial weight. -/
theorem exists_norm_pow_mul_norm_iteratedDeriv_inverseFourier_primitive_symbol_le
    (a : ℝ → ℂ) (ha : a.HasTemperateGrowth) (r : ℝ)
    (hRecip : ∀ x : ℝ, r ≤ |x| →
      a x = ((2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ))⁻¹)
    (j m : ℕ) (hm : j + 2 ≤ m) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |x| ^ k * ‖iteratedDeriv j (𝓕⁻ (a ^ m)) x‖ ≤ C := by
  rw [iteratedDeriv_inverseFourier_pow_fourier_primitive_symbol a ha.1.continuous r hRecip j m hm]
  let f : ℝ → ℂ := fun x => ((2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)) ^ j * a x ^ m
  have hd : ContDiff ℝ ∞ (fun x : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  have hf : ContDiff ℝ ∞ f := (hd.pow j).mul (ha.1.pow m)
  refine ⟨‖2 * (Real.pi : ℂ) * Complex.I‖⁻¹ ^ k * ∫ t : ℝ, ‖iteratedDeriv k f t‖,
    mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _), fun x => ?_⟩
  exact norm_pow_mul_norm_inverseFourier_le f hf
    (integrable_iteratedDeriv_fourier_primitive_moment a ha r hRecip j m hm) k x

private def primitiveFrequencyCutoffError (f : ℝ → ℂ) (N : ℕ) : ℝ → ℂ :=
  (⇑(scaledCompactSchwartzCutoff N) - fun _ => 1) * f

private theorem contDiff_primitiveFrequencyCutoffError {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (N : ℕ) : ContDiff ℝ ∞ (primitiveFrequencyCutoffError f N) :=
  (((scaledCompactSchwartzCutoff N).smooth (⊤ : ℕ∞)).sub contDiff_const).mul hf

private theorem integrable_and_tendsto_norm_iteratedDeriv_primitiveFrequencyCutoffError
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hIntegrable : ∀ k : ℕ, Integrable (iteratedDeriv k f)) (k : ℕ) :
    (∀ N : ℕ, Integrable (iteratedDeriv k (primitiveFrequencyCutoffError f N))) ∧
    Tendsto (fun N : ℕ => ∫ x : ℝ, ‖iteratedDeriv k (primitiveFrequencyCutoffError f N) x‖)
      atTop (𝓝 0) := by
  classical
  let B (i : ℕ) := 2 + SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff
  let D (x : ℝ) := ∑ i ∈ Finset.range (k + 1),
    (↑(k.choose i) * B i) * ‖iteratedDeriv (k - i) f x‖
  have hD : Integrable D := by
    refine integrable_finsetSum _ fun i _ => ?_
    exact (hIntegrable (k - i)).norm.const_mul _
  have hCut (N i : ℕ) (x : ℝ) :
      ‖iteratedDeriv i (fun y : ℝ => scaledCompactSchwartzCutoff N y - 1) x‖ ≤ B i := by
    by_cases hi : i = 0
    · subst i
      rw [iteratedDeriv_zero]
      exact (norm_scaledCompactSchwartzCutoff_sub_one_le_two N x).trans
        (le_add_of_nonneg_right (apply_nonneg _ _))
    · exact (norm_iteratedDeriv_scaledCompactSchwartzCutoff_sub_one_le N i hi x).trans
        ((mul_le_of_le_one_left (apply_nonneg _ _)
          (compactSchwartzCutoffScale_le_one N)).trans (le_add_of_nonneg_left (by norm_num)))
  have hCont (N : ℕ) : Continuous (iteratedDeriv k (primitiveFrequencyCutoffError f N)) :=
    (contDiff_primitiveFrequencyCutoffError hf N).continuous_iteratedDeriv k (by simp)
  have hBound (N : ℕ) (x : ℝ) : ‖iteratedDeriv k (primitiveFrequencyCutoffError f N) x‖ ≤ D x := by
    change ‖iteratedDeriv k ((fun y : ℝ => scaledCompactSchwartzCutoff N y - 1) * f) x‖ ≤ D x
    rw [iteratedDeriv_mul (((scaledCompactSchwartzCutoff N).smooth k).contDiffAt.sub contDiffAt_const)
      ((hf.of_le (by simp : (k : WithTop ℕ∞) ≤ ∞)).contDiffAt)]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    simp only [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hCut N i x) (Nat.cast_nonneg _)) (norm_nonneg _)
  refine ⟨fun N => hD.mono' (hCont N).aestronglyMeasurable (Eventually.of_forall (hBound N)), ?_⟩
  have hLim (x : ℝ) : Tendsto (fun N : ℕ =>
      ‖iteratedDeriv k (primitiveFrequencyCutoffError f N) x‖) atTop (𝓝 (0 : ℝ)) := by
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt |x|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hN' : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
    have hX : |x| < (N : ℝ) + 1 := by linarith
    have hOpen : IsOpen {y : ℝ | |y| < (N : ℝ) + 1} := isOpen_lt continuous_abs continuous_const
    have hLocal : primitiveFrequencyCutoffError f N =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hOpen.mem_nhds hX] with y hy
      have hCutOne : scaledCompactSchwartzCutoff N y = 1 :=
        scaledCompactSchwartzCutoff_eq_one N (show |y| < (N : ℝ) + 1 from hy).le
      simp [primitiveFrequencyCutoffError, hCutOne]
    simp [hLocal.iteratedDeriv_eq k]
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (f := fun _ => (0 : ℝ)) D (fun N => (hCont N).norm.aestronglyMeasurable) hD
    (fun N => Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hBound N x)
    (Eventually.of_forall hLim)

private theorem inverseFourier_add_of_integrable
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕⁻ (f + g) = 𝓕⁻ f + 𝓕⁻ g := by
  exact VectorFourier.fourierIntegral_add (L := -innerₗ ℝ)
    Real.continuous_fourierChar ((continuous_fst.inner continuous_snd).neg) hf hg

/-- The inverse Fourier transform of the primitive symbol with the
repository's smooth expanding frequency cutoff. -/
def fourierPrimitiveSchwartzApproximation (a : ℝ → ℂ) (m N : ℕ) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (a ^ m) (scaledCompactSchwartzCutoff N))

/-- Expanded smooth frequency cutoffs approximate the primitive kernel
uniformly in each polynomial weight and each admitted derivative. -/
theorem eventually_weighted_deriv_fourierPrimitiveSchwartzApproximation
    (a : ℝ → ℂ) (ha : a.HasTemperateGrowth) (r : ℝ)
    (hRecip : ∀ x : ℝ, r ≤ |x| →
      a x = ((2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ))⁻¹)
    (j m : ℕ) (hm : j + 2 ≤ m) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, |x| ^ k *
      ‖iteratedDeriv j (fourierPrimitiveSchwartzApproximation a m N) x -
        iteratedDeriv j (𝓕⁻ (a ^ m)) x‖ < ε := by
  let d : ℝ → ℂ := fun x => (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)
  let f : ℝ → ℂ := fun x => d x ^ j * a x ^ m
  have hd : ContDiff ℝ ∞ d := contDiff_const.mul Complex.ofRealCLM.contDiff
  have hf : ContDiff ℝ ∞ f := (hd.pow j).mul (ha.1.pow m)
  have hI : ∀ l : ℕ, Integrable (iteratedDeriv l f) :=
    integrable_iteratedDeriv_fourier_primitive_moment a ha r hRecip j m hm
  have hIf : Integrable f := by simpa only [iteratedDeriv_zero] using hI 0
  obtain ⟨_, hLim⟩ := integrable_and_tendsto_norm_iteratedDeriv_primitiveFrequencyCutoffError hf hI k
  let C : ℝ := ‖2 * (Real.pi : ℂ) * Complex.I‖⁻¹ ^ k
  have hErr : Tendsto (fun N : ℕ => C *
      ∫ x : ℝ, ‖iteratedDeriv k (primitiveFrequencyCutoffError f N) x‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hLim.const_mul C
  filter_upwards [hErr.eventually (eventually_lt_nhds hε)] with N hN
  intro x
  let g := SchwartzMap.smulLeftCLM ℂ (a ^ m) (scaledCompactSchwartzCutoff N)
  have hg (i : ℕ) (_hi : i ≤ (j : ℕ∞)) : Integrable (fun y : ℝ => y ^ i • g y) := by
    have hCont : Continuous (fun y : ℝ => y ^ i • g y) := by fun_prop
    apply (integrable_norm_iff hCont.aestronglyMeasurable).mp
    simpa only [norm_smul, norm_pow] using g.integrable_pow_mul volume i
  let E := primitiveFrequencyCutoffError f N
  have hE (l : ℕ) : Integrable (iteratedDeriv l E) :=
    (integrable_and_tendsto_norm_iteratedDeriv_primitiveFrequencyCutoffError hf hI l).1 N
  have hEI : Integrable E := by simpa only [iteratedDeriv_zero] using hE 0
  have hProd : (fun y : ℝ => d y ^ j * g y) = E + f := by
    funext y
    rw [show g y = a y ^ m * scaledCompactSchwartzCutoff N y from
      SchwartzMap.smulLeftCLM_apply_apply (ha.pow m) _ _]
    simp only [E, primitiveFrequencyCutoffError, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, f]
    ring
  have hK : (fourierPrimitiveSchwartzApproximation a m N : ℝ → ℂ) = 𝓕⁻ (g : ℝ → ℂ) :=
    SchwartzMap.fourierInv_coe g
  rw [hK, iteratedDeriv_inverseFourier_eq_of_integrable_moments _ j hg,
    iteratedDeriv_inverseFourier_pow_fourier_primitive_symbol a ha.1.continuous r hRecip j m hm]
  change |x| ^ k * ‖(𝓕⁻ (fun y : ℝ => d y ^ j * g y)) x - (𝓕⁻ f) x‖ < ε
  rw [hProd, inverseFourier_add_of_integrable hEI hIf, Pi.add_apply, add_sub_cancel_right]
  exact (norm_pow_mul_norm_inverseFourier_le E (contDiff_primitiveFrequencyCutoffError hf N)
    hE k x).trans_lt hN

/-- A smooth function with integrable derivatives of all orders admits
compact Schwartz cutoffs whose inverse transforms converge uniformly
in every integral polynomial weight. -/
theorem eventually_weighted_inverseFourier_schwartzCutoff
    (f : ℝ → ℂ) (hf : f.HasTemperateGrowth)
    (hInt : ∀ j : ℕ, Integrable (iteratedDeriv j f))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x| ^ k * ‖(𝓕⁻ (SchwartzMap.smulLeftCLM ℂ f (scaledCompactSchwartzCutoff N))) x -
        (𝓕⁻ f) x‖ < ε := by
  have hIf : Integrable f := by simpa only [iteratedDeriv_zero] using hInt 0
  obtain ⟨_, hLim⟩ := integrable_and_tendsto_norm_iteratedDeriv_primitiveFrequencyCutoffError hf.1 hInt k
  let C : ℝ := ‖2 * (Real.pi : ℂ) * Complex.I‖⁻¹ ^ k
  have hErr : Tendsto (fun N : ℕ => C *
      ∫ x : ℝ, ‖iteratedDeriv k (primitiveFrequencyCutoffError f N) x‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hLim.const_mul C
  filter_upwards [hErr.eventually (eventually_lt_nhds hε)] with N hN
  intro x
  let g := SchwartzMap.smulLeftCLM ℂ f (scaledCompactSchwartzCutoff N)
  let E := primitiveFrequencyCutoffError f N
  have hL : Integrable E := by
    have h := (integrable_and_tendsto_norm_iteratedDeriv_primitiveFrequencyCutoffError hf.1 hInt 0).1 N
    simpa only [iteratedDeriv_zero] using h
  have hProd : (g : ℝ → ℂ) = E + f := by
    funext y
    rw [show g y = f y * scaledCompactSchwartzCutoff N y from
      SchwartzMap.smulLeftCLM_apply_apply hf _ _]
    simp only [E, primitiveFrequencyCutoffError, Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
    ring
  change |x| ^ k * ‖(𝓕⁻ g) x - (𝓕⁻ f) x‖ < ε
  rw [show (𝓕⁻ g : SchwartzMap ℝ ℂ) x = (𝓕⁻ (g : ℝ → ℂ)) x from
    congrFun (SchwartzMap.fourierInv_coe g) x]
  rw [hProd, inverseFourier_add_of_integrable hL hIf, Pi.add_apply, add_sub_cancel_right]
  exact (norm_pow_mul_norm_inverseFourier_le E (contDiff_primitiveFrequencyCutoffError hf.1 N)
    (fun j => (integrable_and_tendsto_norm_iteratedDeriv_primitiveFrequencyCutoffError hf.1 hInt j).1 N)
    k x).trans_lt hN


/-- The same cutoff approximation controls the exact weight used for
absolute variation of original atomic records. -/
theorem eventually_one_add_abs_pow_inverseFourier_schwartzCutoff
    (f : ℝ → ℂ) (hf : f.HasTemperateGrowth)
    (hInt : ∀ j : ℕ, Integrable (iteratedDeriv j f))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      (1 + |x|) ^ k * ‖(𝓕⁻ (SchwartzMap.smulLeftCLM ℂ f (scaledCompactSchwartzCutoff N))) x -
        (𝓕⁻ f) x‖ < ε := by
  let d : ℝ := ε / 2 ^ k
  have hd : 0 < d := by dsimp [d]; positivity
  filter_upwards [eventually_weighted_inverseFourier_schwartzCutoff f hf hInt 0 d hd,
    eventually_weighted_inverseFourier_schwartzCutoff f hf hInt k d hd] with N h₀ hk
  intro x
  let e := ‖(𝓕⁻ (SchwartzMap.smulLeftCLM ℂ f (scaledCompactSchwartzCutoff N))) x - (𝓕⁻ f) x‖
  have h₀x : e < d := by simpa only [pow_zero, one_mul] using h₀ x
  have h₁ : 0 < (2 : ℝ) ^ k := by positivity
  have hScale : (2 : ℝ) ^ k * d = ε := by dsimp [d]; field_simp
  by_cases hx : |x| ≤ 1
  · calc
      (1 + |x|) ^ k * e ≤ 2 ^ k * e :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) _) (norm_nonneg _)
      _ < _ := (mul_lt_mul_of_pos_left h₀x h₁).trans_eq hScale
  · have h : 1 + |x| ≤ 2 * |x| := by linarith [lt_of_not_ge hx]
    calc
      (1 + |x|) ^ k * e ≤ (2 * |x|) ^ k * e :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h _) (norm_nonneg _)
      _ = 2 ^ k * (|x| ^ k * e) := by rw [mul_pow, mul_assoc]
      _ < _ := (mul_lt_mul_of_pos_left (hk x) h₁).trans_eq hScale

end
end MeyerGeneralProblem
