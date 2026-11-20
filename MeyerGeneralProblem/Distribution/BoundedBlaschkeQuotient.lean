module

public import MeyerGeneralProblem.Distribution.BlaschkeHalfPlaneJensen
public import MeyerGeneralProblem.Distribution.DiskPositivePoissonRepresentation
public import Mathlib.Analysis.Complex.Schwarz

@[expose] public section

/-!
# Bounds for the zero-free Blaschke quotient

The Gaussian Fourier integral bounds the heated transform on the
closed upper half-plane. The Schwarz lemma in a chart centered at
each zero transfers a bound through finite Blaschke division.
-/

namespace MeyerGeneralProblem

noncomputable section

open ComplexConjugate Filter MeasureTheory Metric Set
open scoped FourierTransform Topology

/-- At fixed positive heat time the normalized transform is bounded
on the closed upper half-plane by the integrable Fourier mass. -/
theorem norm_edgeNormalizedHeatFourierLaplace_le_fourier_mass
    {f : ℝ → ℝ} (hf : Integrable f) {t : ℝ} (ht : 0 < t) (b : ℝ)
    {z : ℂ} (hz : 0 ≤ z.im) :
    ‖edgeNormalizedHeatFourierLaplace t f b z‖ ≤
      ∫ ξ : ℝ, ‖(𝓕 (fun x : ℝ => (realGaussianSmoothing t f x : ℂ))) ξ‖ := by
  let F := 𝓕 (fun x : ℝ => (realGaussianSmoothing t f x : ℂ))
  let A (a : ℝ) : ℂ := ((↑(2 * Real.pi * a) : ℂ) * Complex.I) * z
  let K (ξ : ℝ) := Complex.exp (-(A b)) * (F ξ * Complex.exp (A ξ))
  have hNorm (a : ℝ) : (A a).re = -(2 * Real.pi * a) * z.im := by
    simp only [A, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, mul_one, add_zero, zero_sub,
      neg_mul]
  have hK (ξ : ℝ) (hξ : b < ξ) : ‖K ξ‖ ≤ ‖F ξ‖ := by
    have hExp : Real.exp (-(A b).re) * Real.exp (A ξ).re ≤ 1 := by
      rw [← Real.exp_add, Real.exp_le_one_iff, hNorm, hNorm]
      have h := mul_nonneg (sub_nonneg.mpr hξ.le) (mul_nonneg Real.two_pi_pos.le hz)
      nlinarith only [h]
    calc
      _ = ‖F ξ‖ * (Real.exp (-(A b).re) * Real.exp (A ξ).re) := by
        simp only [K, norm_mul, Complex.norm_exp, Complex.neg_re]
        ring
      _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) hExp
  have hF : Integrable F := integrable_fourier_realGaussianSmoothing hf ht
  have hEq : edgeNormalizedHeatFourierLaplace t f b z = ∫ ξ in Ioi b, K ξ := by
    dsimp only [edgeNormalizedHeatFourierLaplace, heatFourierLaplace]
    rw [← integral_const_mul]
    apply integral_congr_ae
    refine ae_of_all _ fun ξ => ?_
    simp only [K, F, A, neg_mul]
  rw [hEq]
  calc
    _ ≤ ∫ ξ in Ioi b, ‖K ξ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ ξ in Ioi b, ‖F ξ‖ := by
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hF.norm.integrableOn ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
      exact hK ξ hξ
    _ ≤ _ := setIntegral_le_integral hF.norm (ae_of_all _ (fun _ => norm_nonneg _))

private theorem upperHalfPlaneBlaschkeFactor_eq_scaledUpperHalfPlaneToDisk (w z : ℂ) :
    upperHalfPlaneBlaschkeFactor w z =
      scaledUpperHalfPlaneToDisk w.im (z - (w.re : ℂ)) := by
  have hNum : z - (w.re : ℂ) - (w.im : ℂ) * Complex.I = z - w := by
    rw [sub_sub, Complex.re_add_im]
  have hDen : z - (w.re : ℂ) + (w.im : ℂ) * Complex.I = z - conj w := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  rw [upperHalfPlaneBlaschkeFactor, scaledUpperHalfPlaneToDisk, hNum, hDen]

private theorem norm_upperHalfPlaneBlaschkeFactor_at_zero {w : ℂ} (hw : 0 < w.im) :
    ‖upperHalfPlaneBlaschkeFactor w 0‖ = 1 := by
  rw [← Complex.ofReal_zero, ← exp_upperHalfPlaneBlaschkePhase hw 0, Complex.norm_exp]
  simp [Complex.mul_re]

private theorem norm_le_of_normalizedBlaschkeFactor_mul {G : ℂ → ℂ} {w : ℂ}
    (hw : 0 < w.im) (hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.im}) {M : ℝ}
    (hMul : ∀ z : ℂ, 0 < z.im → ‖upperHalfPlaneNormalizedBlaschkeFactor w z * G z‖ ≤ M)
    {z : ℂ} (hz : 0 < z.im) : ‖G z‖ ≤ M := by
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  let C (q : ℂ) := (w.im : ℂ) * cayleyToUpperHalfPlane q + (w.re : ℂ)
  let A (z : ℂ) := upperHalfPlaneNormalizedBlaschkeFactor w z * G z
  let F := A ∘ C
  have hMap : MapsTo C (ball 0 1) U := by
    intro q hq
    have h := im_cayleyToUpperHalfPlane_pos (mem_ball_zero_iff.mp hq)
    change 0 < (C q).im
    simp only [C, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos hw h
  have hDiff : DifferentiableOn ℂ F (ball 0 1) :=
    (((differentiableOn_upperHalfPlaneNormalizedBlaschkeFactor hw).mono
      (fun _ hz => (show 0 < Complex.im _ from hz).le)).mul hG).comp
        ((differentiableOn_cayleyToUpperHalfPlane.const_mul _).add_const _) hMap
  have hC₀ : C 0 = w := by
    have h : cayleyToUpperHalfPlane 0 = Complex.I := by simp [cayleyToUpperHalfPlane]
    dsimp only [C]
    rw [h, add_comm, Complex.re_add_im]
  have hF₀ : F 0 = 0 := by
    simp [F, Function.comp_apply, hC₀, A, upperHalfPlaneNormalizedBlaschkeFactor,
      upperHalfPlaneBlaschkeFactor]
  have hTarget : MapsTo F (ball 0 1) (closedBall (F 0) M) := by
    intro q hq
    rw [hF₀, mem_closedBall, dist_zero_right]
    exact hMul (C q) (hMap hq)
  have hBound (x : ℂ) (hx : 0 < x.im) (hxw : x ≠ w) : ‖G x‖ ≤ M := by
    let q := scaledUpperHalfPlaneToDisk w.im (x - (w.re : ℂ))
    have hx' : 0 < (x - (w.re : ℂ)).im := by simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hx
    have hq : ‖q‖ < 1 := norm_scaledUpperHalfPlaneToDisk_lt_one hx' hw
    have hC : C q = x := by
      dsimp only [C, q]
      rw [scaled_cayleyToUpperHalfPlane_scaledUpperHalfPlaneToDisk hx' hw, sub_add_cancel]
    have hNe : q ≠ 0 := by
      intro he
      exact hxw (hC.symm.trans (he ▸ hC₀))
    have hA := Complex.dist_le_div_mul_dist_of_mapsTo_ball hDiff hTarget (mem_ball_zero_iff.mpr hq)
    have hA₀ : A (C 0) = 0 := hF₀
    have hNorm : ‖A x‖ ≤ M * ‖q‖ := by
      simpa only [F, Function.comp_apply, hC, hA₀, dist_zero_right, div_one] using hA
    dsimp only [A, upperHalfPlaneNormalizedBlaschkeFactor] at hNorm
    rw [norm_mul, norm_div, norm_upperHalfPlaneBlaschkeFactor_at_zero hw, div_one,
      upperHalfPlaneBlaschkeFactor_eq_scaledUpperHalfPlaneToDisk, mul_comm M] at hNorm
    exact (mul_le_mul_iff_of_pos_left (norm_pos_iff.mpr hNe)).mp hNorm
  by_cases hzw : z = w
  · subst z
    have hOpen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
    have hCont : ContinuousAt (fun x => ‖G x‖) w :=
      (hG.continuousOn.continuousAt (hOpen.mem_nhds hw)).norm
    apply le_of_tendsto (hCont.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun x => ‖G x‖) (𝓝[≠] w) (𝓝 ‖G w‖))
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hOpen.mem_nhds hw),
      self_mem_nhdsWithin (s := ({w} : Set ℂ)ᶜ)] with x hx hNe
    exact hBound x hx hNe
  · exact hBound z hz hzw

private theorem norm_le_of_finset_normalizedBlaschkeFactor_mul {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (s : Finset ι) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.im}) {M : ℝ}
    (hMul : ∀ z : ℂ, 0 < z.im →
      ‖(∏ i ∈ s, upperHalfPlaneNormalizedBlaschkeFactor (w i) z) * G z‖ ≤ M)
    {z : ℂ} (hz : 0 < z.im) : ‖G z‖ ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, one_mul] using hMul z hz
  | @insert i s hi ih =>
    apply ih
    intro x hx
    let J (z : ℂ) := (∏ j ∈ s, upperHalfPlaneNormalizedBlaschkeFactor (w j) z) * G z
    have hDiff : DifferentiableOn ℂ J {z : ℂ | 0 < z.im} :=
      ((differentiableOn_finset_normalizedBlaschkeFactor_prod hw s).mono
        (fun _ hz => (show 0 < Complex.im _ from hz).le)).mul hG
    apply norm_le_of_normalizedBlaschkeFactor_mul (hw i) hDiff _ hx
    intro u hu
    simpa only [Finset.prod_insert hi, mul_assoc, J] using hMul u hu

/-- A bound on an entire function survives division by its full
Blaschke product when the quotient is analytic. -/
theorem norm_le_of_upperHalfPlaneBlaschkeProduct_mul {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hFin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hWeight : Summable (fun i => upperHalfPlaneBlaschkeWeight (w i)))
    {H G : ℂ → ℂ} (hH : Differentiable ℂ H) (hH₀ : ∃ y, H y ≠ 0)
    (hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.im})
    (hEq : EqOn H (fun z => upperHalfPlaneBlaschkeProduct w z * G z) {z : ℂ | 0 < z.im})
    {M : ℝ} (hBound : ∀ z : ℂ, 0 < z.im → ‖H z‖ ≤ M)
    {z : ℂ} (hz : 0 < z.im) : ‖G z‖ ≤ M := by
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  have hOpen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hPartial (s : Finset ι) (x : ℂ) (hx : 0 < x.im) :
      ‖H x‖ ≤ M * ‖∏ i ∈ s, upperHalfPlaneNormalizedBlaschkeFactor (w i) x‖ := by
    let v (i : {i // i ∉ s}) := w i.1
    let J (x : ℂ) := upperHalfPlaneBlaschkeProduct v x * G x
    have hV (R : ℝ) : {i | ‖v i‖ ≤ R}.Finite :=
      (hFin R).preimage Subtype.val_injective.injOn
    have hW : Summable (fun i => upperHalfPlaneBlaschkeWeight (v i)) :=
      hWeight.subtype (fun i => i ∉ s)
    have hLocal := hasProdLocallyUniformlyOn_upperHalfPlaneBlaschkeProduct (w := v)
      (fun i => hw i.1) hV hW
    have hSplit (u : ℂ) (hu : 0 < u.im) :
        H u = (∏ i ∈ s, upperHalfPlaneNormalizedBlaschkeFactor (w i) u) * J u := by
      have hTail : HasProd (fun i => upperHalfPlaneNormalizedBlaschkeFactor (v i) u)
          (upperHalfPlaneBlaschkeProduct v u) :=
        hLocal.hasProd (show u ∈ {x : ℂ | 0 ≤ x.im} from hu.le)
      have hp := upperHalfPlaneBlaschkeProduct_split s hTail
      calc
        _ = upperHalfPlaneBlaschkeProduct w u * G u := hEq hu
        _ = _ := by rw [hp, mul_assoc]
    have hDiff : DifferentiableOn ℂ J U :=
      (differentiableOn_upperHalfPlaneBlaschkeProduct (w := v) (fun i => hw i.1) hV hW).mul hG
    have hJ : ‖J x‖ ≤ M :=
      norm_le_of_finset_normalizedBlaschkeFactor_mul hw s hDiff
        (fun u hu => hSplit u hu ▸ hBound u hu) hx
    rw [hSplit x hx, norm_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left hJ (norm_nonneg _)
  have hNoZero (x : ℂ) (hx : 0 < x.im) (hxH : H x ≠ 0) : ‖G x‖ ≤ M := by
    have hProd : Tendsto (fun s : Finset ι => ∏ i ∈ s, upperHalfPlaneNormalizedBlaschkeFactor (w i) x)
        atTop (𝓝 (upperHalfPlaneBlaschkeProduct w x)) :=
      (hasProdLocallyUniformlyOn_upperHalfPlaneBlaschkeProduct hw hFin hWeight).hasProd
        (show x ∈ {z : ℂ | 0 ≤ z.im} from hx.le)
    have hLim : Tendsto (fun s : Finset ι =>
        M * ‖∏ i ∈ s, upperHalfPlaneNormalizedBlaschkeFactor (w i) x‖)
        atTop (𝓝 (M * ‖upperHalfPlaneBlaschkeProduct w x‖)) :=
      ((continuous_const.mul continuous_norm).continuousAt.tendsto.comp hProd)
    have h := ge_of_tendsto hLim (Eventually.of_forall (fun s => hPartial s x hx))
    have hEqx : H x = upperHalfPlaneBlaschkeProduct w x * G x := hEq hx
    have hB : upperHalfPlaneBlaschkeProduct w x ≠ 0 := by
      intro he
      exact hxH (hEqx.trans (by simp [he]))
    rw [hEqx, norm_mul, mul_comm M] at h
    exact (mul_le_mul_iff_of_pos_left (norm_pos_iff.mpr hB)).mp h
  have hNonzeroNear : ∀ᶠ x : ℂ in 𝓝[≠] z, H x ≠ 0 := by
    have hA : AnalyticOnNhd ℂ H univ := hH.differentiableOn.analyticOnNhd isOpen_univ
    obtain ⟨y, hy⟩ := hH₀
    have hCod := hA.preimage_zero_mem_codiscrete hy
    change H ⁻¹' {(0 : ℂ)}ᶜ ∈ codiscreteWithin (univ : Set ℂ) at hCod
    have h := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hCod) z (mem_univ z)
    have hMem : H ⁻¹' {(0 : ℂ)}ᶜ ∈ 𝓝[≠] z := by
      simpa only [compl_univ, union_empty] using h
    filter_upwards [hMem] with x hx
    exact hx
  have hCont : ContinuousAt (fun x => ‖G x‖) z :=
    (hG.continuousOn.continuousAt (hOpen.mem_nhds hz)).norm
  apply le_of_tendsto (hCont.tendsto.mono_left nhdsWithin_le_nhds :
    Tendsto (fun x => ‖G x‖) (𝓝[≠] z) (𝓝 ‖G z‖))
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hOpen.mem_nhds hz), hNonzeroNear] with x hx hxH
  exact hNoZero x hx hxH

/-- The actual edge-normalized heat factorization has an analytic
logarithmic remainder with real part bounded from above. -/
theorem eventually_edgeNormalizedHeat_blaschke_factorization_re_le
    {f : ℝ → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 ≤ b)
    (hEdge : ∀ c > b, ∃ ξ ∈ Ioo b c, 𝓕 (fun x : ℝ => (f x : ℂ)) ξ ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let H := edgeNormalizedHeatFourierLaplace t f b
      let B := upperHalfPlaneBlaschkeProduct (upperHalfPlaneZeroAtIndex H)
      let U : Set ℂ := {z : ℂ | 0 < z.im}
      let M := 1 + ∫ ξ : ℝ, ‖(𝓕 (fun x : ℝ => (realGaussianSmoothing t f x : ℂ))) ξ‖
      Summable (fun i : UpperHalfPlaneZeroIndex H =>
        upperHalfPlaneBlaschkeWeight (upperHalfPlaneZeroAtIndex H i)) ∧
      (∀ R : ℝ, {i : UpperHalfPlaneZeroIndex H | ‖upperHalfPlaneZeroAtIndex H i‖ ≤ R}.Finite) ∧
      ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L U ∧ EqOn H (fun z => B z * Complex.exp (L z)) U ∧
        ∀ z ∈ U, (L z).re ≤ Real.log M := by
  obtain ⟨y, _, h⟩ := exists_height_eventually_summable_edgeNormalizedHeat_weightedZeroOrder hf hb hEdge
  have hPos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hPos, h, eventually_edgeNormalizedHeat_has_blaschke_exponential_factorization hf hb hEdge]
    with t ht hZero hF
  obtain ⟨hSum, hFin, L, hL, hEq⟩ := hF
  refine ⟨hSum, hFin, L, hL, hEq, ?_⟩
  intro z hz
  have hH := differentiable_edgeNormalizedHeatFourierLaplace hf ht b
  have hH₀ : ∃ x, edgeNormalizedHeatFourierLaplace t f b x ≠ 0 :=
    ⟨(y : ℂ) * Complex.I, hZero.1⟩
  have hG : DifferentiableOn ℂ (fun z => Complex.exp (L z)) {z : ℂ | 0 < z.im} :=
    Complex.differentiable_exp.comp_differentiableOn hL.differentiableOn
  have hBound (x : ℂ) (hx : 0 < x.im) :
      ‖edgeNormalizedHeatFourierLaplace t f b x‖ ≤
        1 + ∫ ξ : ℝ, ‖(𝓕 (fun x : ℝ => (realGaussianSmoothing t f x : ℂ))) ξ‖ :=
    (norm_edgeNormalizedHeatFourierLaplace_le_fourier_mass hf ht b hx.le).trans
      (le_add_of_nonneg_left zero_le_one)
  have he := norm_le_of_upperHalfPlaneBlaschkeProduct_mul (fun i => i.1.2) hFin hSum
    hH hH₀ hG hEq hBound hz
  rw [Complex.norm_exp] at he
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) he

/-- In Cayley coordinates the nonnegative deficit from an upper bound
on the real part of a holomorphic function has a positive boundary measure. -/
theorem exists_diskBoundaryPoissonMeasure_of_upperHalfPlane_re_le
    {L : ℂ → ℂ} {A : ℝ} (hL : DifferentiableOn ℂ L {z : ℂ | 0 < z.im})
    (hBound : ∀ z : ℂ, 0 < z.im → (L z).re ≤ A) :
    ∃ μ : FiniteMeasure DiskUnitBoundary, ∀ w ∈ ball (0 : ℂ) 1,
      (∫ ζ, diskBoundaryPoissonKernel w ζ ∂(μ : Measure DiskUnitBoundary)) =
        A - (L (cayleyToUpperHalfPlane w)).re := by
  have hMap : MapsTo cayleyToUpperHalfPlane (ball (0 : ℂ) 1) {z : ℂ | 0 < z.im} :=
    fun _ hw => im_cayleyToUpperHalfPlane_pos (mem_ball_zero_iff.mp hw)
  let F (w : ℂ) := (A : ℂ) - L (cayleyToUpperHalfPlane w)
  have hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1) :=
    (differentiableOn_const (A : ℂ)).sub (hL.comp differentiableOn_cayleyToUpperHalfPlane hMap)
  have hPos (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : 0 ≤ (F w).re := by
    simpa only [F, Complex.sub_re, Complex.ofReal_re] using sub_nonneg.mpr (hBound _ (hMap hw))
  obtain ⟨μ, _, hμ⟩ := exists_diskBoundaryPoissonMeasure hF hPos
  refine ⟨μ, fun w hw => ?_⟩
  simpa only [F, Complex.sub_re, Complex.ofReal_re] using hμ w hw

end
end MeyerGeneralProblem
