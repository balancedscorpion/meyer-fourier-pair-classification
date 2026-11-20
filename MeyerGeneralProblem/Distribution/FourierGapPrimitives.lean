module

public import MeyerGeneralProblem.UniformDiscrete.SpectralWindow
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# Tempered primitives with a centered Fourier gap

A smooth reciprocal of the derivative symbol outside the gap gives
arbitrarily many distributional primitives with the same gap.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter LineDeriv MeasureTheory Metric Set UniformDiscrete
open scoped ContDiff FourierTransform Topology

private theorem exists_temperate_inverse_on_unit_interval {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1) :
    ∃ g : ℝ → ℝ, g.HasTemperateGrowth ∧ ∀ y ∈ Icc δ 1, g y = y⁻¹ := by
  let b : ContDiffBump (1 : ℝ) := ⟨1 - δ, 1 - δ / 2, by linarith, by linarith⟩
  let g : ℝ → ℝ := fun y => b y * y⁻¹
  have hgSupport : tsupport g ⊆ tsupport (b : ℝ → ℝ) := tsupport_mul_subset_left
  have hgCompact : HasCompactSupport g :=
    b.hasCompactSupport.of_isClosed_subset isClosed_closure hgSupport
  have hgSmooth : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y = 0
    · subst y
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hb : (closedBall (1 : ℝ) b.rOut)ᶜ ∈ 𝓝 (0 : ℝ) := by
        apply isClosed_closedBall.isOpen_compl.mem_nhds
        change ¬ dist (0 : ℝ) 1 ≤ 1 - δ / 2
        rw [Real.dist_eq]
        norm_num
        linarith
      filter_upwards [hb] with x hx
      have hxDist : b.rOut ≤ dist x 1 := (not_le.mp (show ¬ dist x 1 ≤ b.rOut from hx)).le
      simp [g, b.zero_of_le_dist hxDist]
    · exact b.contDiff.contDiffAt.mul (contDiffAt_inv ℝ hy)
  refine ⟨g, hgCompact.hasTemperateGrowth hgSmooth, fun y hy => ?_⟩
  have hb : b y = 1 := by
    apply b.one_of_mem_closedBall
    change dist y 1 ≤ 1 - δ
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hy.2)]
    linarith [hy.1]
  simp [g, hb]

private theorem exists_temperate_inverse_off_centered_interval {r : ℝ} (hr : 0 < r) :
    ∃ g : ℝ → ℝ, g.HasTemperateGrowth ∧ ∀ x : ℝ, r ≤ |x| → x * g x = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by positivity, by linarith⟩
  let u : ℝ → ℝ := fun x => (1 + x ^ 2)⁻¹
  have hu : u.HasTemperateGrowth := by
    simpa only [u, Real.norm_eq_abs, sq_abs, Real.rpow_neg_one] using
      Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (-1)
  let f : ℝ → ℝ := fun x => (x ^ 2 + b x) * u x
  have hb : (b : ℝ → ℝ).HasTemperateGrowth := b.hasCompactSupport.hasTemperateGrowth b.contDiff
  have hf : f.HasTemperateGrowth := by dsimp [f]; fun_prop
  let δ := (r / 2) ^ 2 / (1 + (r / 2) ^ 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ' : δ < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  obtain ⟨c, hc, hcVal⟩ := exists_temperate_inverse_on_unit_interval hδ hδ'
  have hfRange (x : ℝ) : f x ∈ Icc δ 1 := by
    have hd : 0 < 1 + x ^ 2 := by positivity
    have hUpper : f x ≤ 1 := by
      change (x ^ 2 + b x) * (1 + x ^ 2)⁻¹ ≤ 1
      rw [← div_eq_mul_inv, div_le_one hd]
      linarith [b.le_one (x := x)]
    refine ⟨?_, hUpper⟩
    by_cases hx : |x| ≤ r / 2
    · have hbOne : b x = 1 := b.one_of_mem_closedBall
        (mem_closedBall.mpr (by simpa only [Real.dist_eq, sub_zero] using hx))
      have hfOne : f x = 1 := by
        simp [f, u, hbOne, add_comm (x ^ 2) 1, hd.ne']
      rw [hfOne]
      exact hδ'.le
    · have hsq : (r / 2) ^ 2 ≤ x ^ 2 := by
        rw [← sq_abs x]
        exact pow_le_pow_left₀ (by positivity) (lt_of_not_ge hx).le 2
      calc
        δ ≤ x ^ 2 / (1 + x ^ 2) := by
          dsimp [δ]
          apply (div_le_div_iff₀ (by positivity) hd).mpr
          nlinarith only [hsq]
        _ ≤ f x := by
          change x ^ 2 / (1 + x ^ 2) ≤ (x ^ 2 + b x) * (1 + x ^ 2)⁻¹
          rw [← div_eq_mul_inv]
          exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (b.nonneg' x)) hd.le
  let g : ℝ → ℝ := fun x => x * u x * c (f x)
  refine ⟨g, ?_, fun x hx => ?_⟩
  · dsimp [g]
    exact ((Function.HasTemperateGrowth.id (E := ℝ)).fun_mul hu).fun_mul (hc.comp hf)
  · have hx0 : x ≠ 0 := by
      rintro rfl
      exact hr.not_ge (by simpa only [abs_zero] using hx)
    have hd : 1 + x ^ 2 ≠ 0 := by positivity
    have hbx : b x = 0 := b.zero_of_le_dist (by simpa only [Real.dist_eq, sub_zero] using hx)
    rw [show g x = x * u x * c (f x) from rfl, hcVal (f x) (hfRange x)]
    simp only [f, u, hbx, add_zero, mul_inv_rev, inv_inv]
    field_simp

private theorem temperedMultiplier_tsupport_subset {g : ℝ → ℂ} (hg : g.HasTemperateGrowth)
    (φ : SchwartzMap ℝ ℂ) :
    tsupport (SchwartzMap.smulLeftCLM ℂ g φ : ℝ → ℂ) ⊆ tsupport (φ : ℝ → ℂ) := by
  have he : (SchwartzMap.smulLeftCLM ℂ g φ : ℝ → ℂ) = fun x => g x * φ x := by
    funext x
    exact SchwartzMap.smulLeftCLM_apply_apply hg φ x
  rw [he]
  exact tsupport_mul_subset_right

/-- Multiplying a tempered distribution by a smooth temperate symbol preserves its gap. -/
theorem vanishesOnInterval_temperedMultiplier {T : TemperedDistribution ℝ ℂ} {R : ℝ}
    (hT : VanishesOnInterval T R) {g : ℝ → ℂ} (hg : g.HasTemperateGrowth) :
    VanishesOnInterval (TemperedDistribution.smulLeftCLM ℂ g T) R := by
  intro φ hφ hSupport
  have hSub := temperedMultiplier_tsupport_subset hg φ
  exact hT _ (hφ.of_isClosed_subset isClosed_closure hSub) (hSub.trans hSupport)

private theorem temperedMultiplier_eq_zero_of_support_inside_gap {T : TemperedDistribution ℝ ℂ}
    {R : ℝ} (hT : VanishesOnInterval T R) {g : ℝ → ℂ} (hg : g.HasTemperateGrowth)
    (hSupport : tsupport g ⊆ Ioo (-R) R) :
    TemperedDistribution.smulLeftCLM ℂ g T = 0 := by
  ext φ
  have he : (SchwartzMap.smulLeftCLM ℂ g φ : ℝ → ℂ) = fun x => g x * φ x := by
    funext x
    exact SchwartzMap.smulLeftCLM_apply_apply hg φ x
  have hSub : tsupport (SchwartzMap.smulLeftCLM ℂ g φ : ℝ → ℂ) ⊆ tsupport g := by
    rw [he]
    exact tsupport_mul_subset_left
  have hCompact : HasCompactSupport (SchwartzMap.smulLeftCLM ℂ g φ : ℝ → ℂ) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (hSub.trans (hSupport.trans Ioo_subset_Icc_self))
  exact hT _ hCompact (hSub.trans hSupport)

private theorem fourier_lineDeriv_multiplier (V : TemperedDistribution ℝ ℂ) :
    𝓕 (lineDerivOp (1 : ℝ) V) = TemperedDistribution.smulLeftCLM ℂ
      (fun x : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)) (𝓕 V) := by
  rw [TemperedDistribution.fourier_lineDerivOp_eq]
  simp only [Real.inner_apply, mul_one]
  have hCoord : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
  change (2 * (Real.pi : ℂ) * Complex.I) •
    TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) (𝓕 V) = _
  rw [← smul_apply, ← TemperedDistribution.smulLeftCLM_smul hCoord]
  rfl

/-- One symbol gives a tempered primitive at every order while preserving the centered gap.
The symbol agrees with the reciprocal of the derivative multiplier outside
any prescribed positive radius strictly inside the gap. -/
theorem exists_fourier_symbol_for_centered_gap_primitives
    (R r : ℝ) (hr : 0 < r) (hrR : r < R) :
    ∃ a : ℝ → ℂ, a.HasTemperateGrowth ∧
      (∀ x : ℝ, r ≤ |x| → a x = ((2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ))⁻¹) ∧
      ∀ U : TemperedDistribution ℝ ℂ, VanishesOnInterval (𝓕 U) R →
        ∃ V : ℕ → TemperedDistribution ℝ ℂ,
          V 0 = U ∧
          (∀ m : ℕ, lineDerivOp (1 : ℝ) (V (m + 1)) = V m) ∧
          (∀ m : ℕ, VanishesOnInterval (𝓕 (V m)) R) ∧
          ∀ m : ℕ, 𝓕 (V m) = TemperedDistribution.smulLeftCLM ℂ (a ^ m) (𝓕 U) := by
  obtain ⟨g, hg, hgInv⟩ := exists_temperate_inverse_off_centered_interval hr
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  let a : ℝ → ℂ := fun x => c⁻¹ * (g x : ℂ)
  have ha : a.HasTemperateGrowth := by
    dsimp [a]
    exact (Function.HasTemperateGrowth.const c⁻¹).fun_mul (Complex.ofRealCLM.hasTemperateGrowth.comp hg)
  let d : ℝ → ℂ := fun x => c * (x : ℂ)
  have hd : d.HasTemperateGrowth := by dsimp [d]; fun_prop
  have haRight (x : ℝ) (hx : r ≤ |x|) : a x * d x = 1 := by
    have hxInv : (x : ℂ) * (g x : ℂ) = 1 := by exact_mod_cast hgInv x hx
    change c⁻¹ * (g x : ℂ) * (c * (x : ℂ)) = 1
    rw [show c⁻¹ * (g x : ℂ) * (c * (x : ℂ)) =
      (c⁻¹ * c) * ((x : ℂ) * (g x : ℂ)) by ring, inv_mul_cancel₀ hc, hxInv, one_mul]
  refine ⟨a, ha, ?_, ?_⟩
  · intro x hx
    change a x = (d x)⁻¹
    exact eq_inv_of_mul_eq_one_right (by simpa only [mul_comm (d x)] using haRight x hx)
  let q : ℝ → ℂ := 1 - a * d
  have hq : q.HasTemperateGrowth := (Function.HasTemperateGrowth.const 1).sub (ha.mul hd)
  have hqSupp : tsupport q ⊆ Ioo (-R) R := by
    refine (closure_minimal (t := closedBall (0 : ℝ) r) ?_ isClosed_closedBall).trans ?_
    · intro x hx
      by_contra hxBall
      have hxFar : r ≤ |x| := (not_le.mp (by
        simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hxBall)).le
      exact hx (sub_eq_zero.mpr (haRight x hxFar).symm)
    · intro x hx
      have hxSmall : |x| ≤ r := by simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hx
      exact abs_lt.mp (hxSmall.trans_lt hrR)
  have hRight (T : TemperedDistribution ℝ ℂ) (hT : VanishesOnInterval T R) :
      TemperedDistribution.smulLeftCLM ℂ (a * d) T = T := by
    have hz := temperedMultiplier_eq_zero_of_support_inside_gap hT hq hqSupp
    change TemperedDistribution.smulLeftCLM ℂ ((fun _ => (1 : ℂ)) - a * d) T = 0 at hz
    rw [TemperedDistribution.smulLeftCLM_sub (Function.HasTemperateGrowth.const 1) (ha.mul hd),
      sub_apply] at hz
    simpa using (sub_eq_zero.mp hz).symm
  intro U hU
  let Fm (m : ℕ) := TemperedDistribution.smulLeftCLM ℂ (a ^ m) (𝓕 U)
  let V (m : ℕ) : TemperedDistribution ℝ ℂ := 𝓕⁻ (Fm m)
  have hFourier (m : ℕ) : 𝓕 (V m) = Fm m := FourierTransform.fourier_fourierInv_eq _
  have hGap (m : ℕ) : VanishesOnInterval (Fm m) R :=
    vanishesOnInterval_temperedMultiplier hU (ha.pow m)
  have hInv (X : TemperedDistribution ℝ ℂ) : 𝓕⁻ (𝓕 X) = X :=
    FourierTransform.fourierInv_fourier_eq X
  refine ⟨V, ?_, ?_, fun m => hFourier m ▸ hGap m, hFourier⟩
  · change 𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (a ^ 0) (𝓕 U)) = U
    simp only [pow_zero]
    change 𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (fun _ => (1 : ℂ)) (𝓕 U)) = U
    simp
  · intro m
    have hFm : Fm (m + 1) = TemperedDistribution.smulLeftCLM ℂ a (Fm m) := by
      unfold Fm
      rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (ha.pow m) ha, pow_succ]
    rw [← hInv (lineDerivOp (1 : ℝ) (V (m + 1))), fourier_lineDeriv_multiplier, hFourier, hFm]
    change 𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ d
      (TemperedDistribution.smulLeftCLM ℂ a (Fm m))) = V m
    rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply ha hd, hRight _ (hGap m)]

/-- Each finite derivative order has a tempered primitive with the original centered gap. -/
theorem exists_tempered_iterated_primitive_with_centered_gap
    (U : TemperedDistribution ℝ ℂ) (R : ℝ) (hR : 0 < R)
    (hGap : VanishesOnInterval (𝓕 U) R) (m : ℕ) :
    ∃ V : TemperedDistribution ℝ ℂ,
      ((lineDerivOp (1 : ℝ))^[m]) V = U ∧ VanishesOnInterval (𝓕 V) R := by
  obtain ⟨_, _, _, hV⟩ := exists_fourier_symbol_for_centered_gap_primitives R (R / 2)
    (half_pos hR) (half_lt_self hR)
  obtain ⟨V, hBase, hDeriv, hVGap, _⟩ := hV U hGap
  refine ⟨V m, ?_, hVGap m⟩
  induction m with
  | zero => exact hBase
  | succ m ih =>
    rw [Function.iterate_succ_apply, hDeriv, ih]

/-- Outside a bounded interval, agreement with the reciprocal derivative
symbol gives all integrable moments of strictly smaller order than (m-1). -/
theorem integrable_norm_pow_mul_norm_fourier_primitive_symbol
    (a : ℝ → ℂ) (ha : Continuous a) (r : ℝ)
    (hRecip : ∀ x : ℝ, r ≤ |x| →
      a x = ((2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ))⁻¹)
    (j m : ℕ) (hm : j + 2 ≤ m) :
    Integrable (fun x : ℝ => ‖x‖ ^ j * ‖a x ^ m‖) := by
  let s := max 1 r
  let c : ℝ := ‖2 * (Real.pi : ℂ) * Complex.I‖⁻¹ ^ m
  let F : ℝ → ℝ := fun x => ‖x‖ ^ j * ‖a x ^ m‖
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hBound (x : ℝ) (hx : s < |x|) : ‖F x‖ ≤ (2 * c) * (1 + x ^ 2)⁻¹ := by
    have hx1 : 1 ≤ |x| := (le_max_left 1 r).trans hx.le
    have hx0 : 0 < |x| := zero_lt_one.trans_le hx1
    have hxa := hRecip x ((le_max_right 1 r).trans hx.le)
    have hNorm : F x = c * (|x| ^ (m - j))⁻¹ := by
      have hmj : m - j + j = m := Nat.sub_add_cancel (by omega)
      have hCancel : |x| ^ j * (|x| ^ m)⁻¹ = (|x| ^ (m - j))⁻¹ := by
        rw [← hmj, pow_add, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero j hx0.ne'), one_mul]
        congr 2
        omega
      dsimp [F, c]
      rw [hxa, norm_pow, norm_inv, norm_mul, Complex.norm_real, mul_inv_rev, mul_pow,
        Real.norm_eq_abs, inv_pow |x| m]
      calc
        _ = ‖2 * (Real.pi : ℂ) * Complex.I‖⁻¹ ^ m * (|x| ^ j * (|x| ^ m)⁻¹) := by ring
        _ = _ := by rw [hCancel]
    have hPow : |x| ^ 2 ≤ |x| ^ (m - j) := pow_le_pow_right₀ hx1 (by omega)
    have hTwo : 1 + x ^ 2 ≤ 2 * |x| ^ 2 := by
      rw [sq_abs]
      have hSq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hx1 2
      rw [one_pow, sq_abs] at hSq
      linarith
    have hInv : (|x| ^ 2)⁻¹ ≤ 2 * (1 + x ^ 2)⁻¹ := by
      have hd : 1 / |x| ^ 2 ≤ 2 / (1 + x ^ 2) :=
        (div_le_div_iff₀ (pow_pos hx0 2) (by positivity : 0 < 1 + x ^ 2)).mpr (by simpa using hTwo)
      simpa only [div_eq_mul_inv, one_mul] using hd
    have hc : 0 ≤ c := by dsimp [c]; positivity
    rw [Real.norm_of_nonneg (by dsimp [F]; positivity), hNorm]
    calc
      c * (|x| ^ (m - j))⁻¹ ≤ c * (|x| ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_le_inv₀ (pow_pos hx0 _) (pow_pos hx0 _)
          |>.mpr hPow) hc
      _ ≤ c * (2 * (1 + x ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hInv hc
      _ = _ := by ring
  have hLocal : IntegrableOn F (closedBall (0 : ℝ) s) :=
    hF.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hTail : IntegrableOn F (closedBall (0 : ℝ) s)ᶜ := by
    apply (integrable_inv_one_add_sq.const_mul (2 * c)).integrableOn.mono' hF.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (isClosed_closedBall.measurableSet.compl)] with x hx
    have hxFar : s < |x| := not_le.mp (by
      simpa only [mem_compl_iff, mem_closedBall, Real.dist_eq, sub_zero] using hx)
    exact hBound x hxFar
  simpa only [union_compl_self, integrableOn_univ] using hLocal.union hTail

/-- Taking enough primitives makes the inverse Fourier kernel continuously
differentiable through any prescribed finite order. -/
theorem contDiff_inverseFourier_pow_fourier_primitive_symbol
    (a : ℝ → ℂ) (ha : Continuous a) (r : ℝ)
    (hRecip : ∀ x : ℝ, r ≤ |x| →
      a x = ((2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ))⁻¹)
    (n m : ℕ) (hm : n + 2 ≤ m) : ContDiff ℝ n (𝓕⁻ (a ^ m)) := by
  have hEq : 𝓕⁻ (a ^ m) = (𝓕 (a ^ m)) ∘ (fun x => -x) := by
    funext x
    exact Real.fourierInv_eq_fourier_neg _ x
  rw [hEq]
  have hF : ContDiff ℝ n (𝓕 (a ^ m)) := by
    apply Real.contDiff_fourier
    intro j hj
    exact integrable_norm_pow_mul_norm_fourier_primitive_symbol a ha r hRecip j m
      ((Nat.add_le_add_right (by exact_mod_cast hj : j ≤ n) 2).trans hm)
  exact hF.comp contDiff_neg

/-- Differentiation under the inverse Fourier integral uses the positive-sign
derivative multiplier when the indicated moments are integrable. -/
theorem iteratedDeriv_inverseFourier_eq_of_integrable_moments
    (f : ℝ → ℂ) (n : ℕ)
    (hMom : ∀ j : ℕ, j ≤ (n : ℕ∞) → Integrable (fun x : ℝ => x ^ j • f x)) :
    iteratedDeriv n (𝓕⁻ f) =
      𝓕⁻ (fun x : ℝ => ((2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)) ^ n * f x) := by
  have he : 𝓕⁻ f = fun x => (𝓕 f) (-x) := by
    funext x
    exact Real.fourierInv_eq_fourier_neg _ x
  funext x
  rw [he, iteratedDeriv_comp_neg, Real.iteratedDeriv_fourier hMom (le_refl (n : ℕ∞)),
    Real.fourierInv_eq_fourier_neg]
  simp only [Real.fourier_eq', ← integral_smul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one,
    smul_eq_mul]
  have hSign : (-1 : ℂ) ^ n * (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ n =
      (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    _ = Complex.exp (↑(-2 * Real.pi * inner ℝ t (-x)) * Complex.I) *
        (((-1 : ℂ) ^ n * (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ n) * f t) := by ac_rfl
    _ = _ := by rw [hSign]

/-- The classical derivatives of the inverse Fourier kernel have the same
multiplier as distributional derivatives, through every integrable order. -/
theorem iteratedDeriv_inverseFourier_pow_fourier_primitive_symbol
    (a : ℝ → ℂ) (ha : Continuous a) (r : ℝ)
    (hRecip : ∀ x : ℝ, r ≤ |x| →
      a x = ((2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ))⁻¹)
    (n m : ℕ) (hm : n + 2 ≤ m) :
    iteratedDeriv n (𝓕⁻ (a ^ m)) =
      𝓕⁻ (fun x : ℝ => ((2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)) ^ n * a x ^ m) := by
  apply iteratedDeriv_inverseFourier_eq_of_integrable_moments
  intro j hj
  have hcont : Continuous (fun x : ℝ => x ^ j • (a ^ m) x) := by fun_prop
  apply (integrable_norm_iff hcont.aestronglyMeasurable).mp
  simpa only [norm_smul, norm_pow, Pi.pow_apply] using
    integrable_norm_pow_mul_norm_fourier_primitive_symbol a ha r hRecip j m
      ((Nat.add_le_add_right (by exact_mod_cast hj : j ≤ n) 2).trans hm)

end
end MeyerGeneralProblem
