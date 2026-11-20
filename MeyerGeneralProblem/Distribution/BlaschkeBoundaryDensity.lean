module

public import MeyerGeneralProblem.Distribution.BlaschkeBoundaryDomination
public import MeyerGeneralProblem.Distribution.DiskPoissonBoundaryDensity

@[expose] public section

/-!
# The boundary density of the Blaschke logarithm

The radial real-part deficit converges almost everywhere to the
deficit of the boundary logarithmic modulus. Compact-arc domination
identifies its Poisson representation up to the mass at infinity.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Metric Set
open scoped FourierTransform Topology

/-- The boundary point corresponding to infinity in the Cayley chart. -/
def diskCayleyInfinity : DiskUnitBoundary := ⟨1, by simp⟩

private theorem injOn_cayleyToUpperHalfPlane_off_one :
    InjOn cayleyToUpperHalfPlane ({(1 : ℂ)} : Set ℂ)ᶜ := by
  intro z hz w hw he
  have hz₁ : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm (show z ≠ 1 from hz))
  have hw₁ : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm (show w ≠ 1 from hw))
  unfold cayleyToUpperHalfPlane at he
  have hc := (div_eq_div_iff hz₁ hw₁).mp he
  have hc' : (1 + z) * (1 - w) = (1 + w) * (1 - z) :=
    mul_left_cancel₀ Complex.I_ne_zero (by simpa only [mul_assoc] using hc)
  linear_combination hc' / 2

/-- The zero set of a nonzero entire function is countable. -/
theorem countable_complex_zeros_of_entire_nonzero {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (hH₀ : ∃ z, H z ≠ 0) :
    (H ⁻¹' {(0 : ℂ)}).Countable := by
  let Z := H ⁻¹' {(0 : ℂ)}
  obtain ⟨z, hz⟩ := hH₀
  have hA : AnalyticOnNhd ℂ H univ := hH.differentiableOn.analyticOnNhd isOpen_univ
  have hCodisc : Zᶜ ∈ codiscrete ℂ := by
    change (H ⁻¹' {(0 : ℂ)})ᶜ ∈ codiscrete ℂ
    rw [← preimage_compl]
    exact hA.preimage_zero_mem_codiscrete hz
  let _ : DiscreteTopology Z := isDiscrete_iff_discreteTopology.mp (compl_mem_codiscrete_iff.mp hCodisc).2
  exact TopologicalSpace.separableSpace_iff_countable.mp inferInstance

private theorem ae_cayley_angle_nonzero_of_entire {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (hH₀ : ∃ z, H z ≠ 0) :
    ∀ᵐ θ ∂diskAngleMeasure, circleMap 0 1 θ ≠ 1 ∧
      H (cayleyToUpperHalfPlane (circleMap 0 1 θ)) ≠ 0 := by
  let C := cayleyToUpperHalfPlane
  let Z := H ⁻¹' {(0 : ℂ)}
  let E := C ⁻¹' Z ∩ ({(1 : ℂ)} : Set ℂ)ᶜ
  have hZ : Z.Countable := countable_complex_zeros_of_entire_nonzero hH hH₀
  have hE : E.Countable :=
    (show MapsTo C E Z from fun _ hx => hx.1).countable_of_injOn
      (injOn_cayleyToUpperHalfPlane_off_one.mono inter_subset_right) hZ
  let _ : NullSingletonClass diskAngleMeasure := by
    unfold diskAngleMeasure
    infer_instance
  have hAvoid : ∀ᵐ θ ∂diskAngleMeasure, circleMap 0 1 θ ∉ ({(1 : ℂ)} ∪ E : Set ℂ) := by
    simp only [ae_iff, not_not]
    change diskAngleMeasure (circleMap 0 1 ⁻¹' ({(1 : ℂ)} ∪ E)) = 0
    exact ((countable_singleton (1 : ℂ)).union hE |>.preimage_circleMap 0 one_ne_zero).measure_zero _
  filter_upwards [hAvoid] with θ hθ
  have hOne : circleMap 0 1 θ ≠ 1 := fun he => hθ (Or.inl he)
  exact ⟨hOne, fun he => hθ (Or.inr ⟨he, hOne⟩)⟩

private theorem ae_tendsto_re_blaschkeBoundaryLog_radial {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, 0 < (a i).im) (hFin : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hSum : Summable (fun i => upperHalfPlaneBlaschkeWeight (a i)))
    {H L : ℂ → ℂ} (hH : Differentiable ℂ H) (hH₀ : ∃ z, H z ≠ 0)
    (hFactor : EqOn H (fun z => upperHalfPlaneBlaschkeProduct a z * Complex.exp (L z))
      {z : ℂ | 0 < z.im}) :
    ∀ᵐ θ ∂diskAngleMeasure, Tendsto (fun r : ℝ => (L (cayleyToUpperHalfPlane (circleMap 0 r θ))).re)
      (𝓝[<] (1 : ℝ)) (𝓝 (Real.log ‖H (cayleyToUpperHalfPlane (circleMap 0 1 θ))‖)) := by
  filter_upwards [ae_cayley_angle_nonzero_of_entire hH hH₀] with θ hθ
  have he (r : ℝ) : circleMap 0 r θ = (r : ℂ) * circleMap 0 1 θ := by
    simp only [circleMap_zero, Complex.ofReal_one, one_mul]
  simpa only [← he] using tendsto_re_blaschkeBoundaryLog_radial_of_nonzero
    ha hFin hSum hH.continuous hFactor (by simp [norm_circleMap_zero]) hθ.1 hθ.2

private theorem tendsto_integral_blaschkeBoundaryLog_test {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, 0 < (a i).im) (hFin : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hSum : Summable (fun i => upperHalfPlaneBlaschkeWeight (a i)))
    {H L : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hFactor : EqOn H (fun z => upperHalfPlaneBlaschkeProduct a z * Complex.exp (L z))
      {z : ℂ | 0 < z.im})
    {A : ℝ} (hBound : ∀ z : ℂ, 0 < z.im → (L z).re ≤ A)
    (hL : DifferentiableOn ℂ L {z : ℂ | 0 < z.im})
    (hLim : ∀ᵐ θ ∂diskAngleMeasure, Tendsto (fun r : ℝ => (L (cayleyToUpperHalfPlane (circleMap 0 r θ))).re)
      (𝓝[<] (1 : ℝ)) (𝓝 (Real.log ‖H (cayleyToUpperHalfPlane (circleMap 0 1 θ))‖)))
    (P : C(DiskUnitBoundary, ℝ)) (hP : ∀ᶠ q in 𝓝 diskCayleyInfinity, P q = 0) :
    Tendsto (fun r : ℝ => ∫ θ, ((A - (L (cayleyToUpperHalfPlane (circleMap 0 r θ))).re) / (2 * Real.pi)) *
      P (diskAnglePoint θ) ∂diskAngleMeasure) (𝓝[<] (1 : ℝ))
      (𝓝 (∫ θ, ((A - Real.log ‖H (cayleyToUpperHalfPlane (circleMap 0 1 θ))‖) / (2 * Real.pi)) *
      P (diskAnglePoint θ) ∂diskAngleMeasure)) := by
  let S := tsupport (P : DiskUnitBoundary → ℝ)
  let K := (fun q : DiskUnitBoundary => (q : ℂ)) '' S
  have hOff : diskCayleyInfinity ∉ S := by
    intro hp
    have hf : ∃ᶠ q in 𝓝 diskCayleyInfinity, q ∈ Function.support P := mem_closure_iff_frequently.mp hp
    obtain ⟨q, hq, hq₀⟩ := (hf.and_eventually hP).exists
    exact hq hq₀
  have hK : IsCompact K := (isClosed_tsupport (P : DiskUnitBoundary → ℝ)).isCompact.image continuous_subtype_val
  have hKsub : K ⊆ sphere (0 : ℂ) 1 \ {1} := by
    rintro q ⟨v, hv, rfl⟩
    refine ⟨v.property, ?_⟩
    intro he
    have hv' : v = diskCayleyInfinity := Subtype.ext (mem_singleton_iff.mp he)
    exact hOff (hv' ▸ hv)
  obtain ⟨M, hM, hM₀, hMaj⟩ :=
    exists_integrable_blaschkeBoundaryLog_radial_bound_on_compact ha hFin hSum hH hFactor hK hKsub A
  have hRadi : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ r ∧ r < 1 := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one), self_mem_nhdsWithin]
      with r (hr : 0 < r) (hr₁ : r < 1)
    exact ⟨hr.le, hr₁⟩
  have hBall {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) (θ : ℝ) : circleMap (0 : ℂ) r θ ∈ ball 0 1 := by
    rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_nonneg hr]
    exact hr₁
  have hAngleMap {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) :
      Continuous (fun θ : ℝ => L (cayleyToUpperHalfPlane (circleMap 0 r θ))) :=
    hL.continuousOn.comp_continuous
      (differentiableOn_cayleyToUpperHalfPlane.continuousOn.comp_continuous (continuous_circleMap _ _) (hBall hr hr₁))
      (fun θ => im_cayleyToUpperHalfPlane_pos (mem_ball_zero_iff.mp (hBall hr hr₁ θ)))
  apply tendsto_integral_filter_of_dominated_convergence (fun θ => (M θ / (2 * Real.pi)) * ‖P‖)
  · filter_upwards [hRadi] with r hr
    exact (((continuous_const.sub (Complex.continuous_re.comp (hAngleMap hr.1 hr.2))).div_const _).mul
      (P.continuous.comp continuous_diskAnglePoint)).aestronglyMeasurable
  · filter_upwards [hRadi, hMaj] with r hr hMθ
    filter_upwards [hMθ] with θ hθ
    by_cases hp : P (diskAnglePoint θ) = 0
    · rw [hp, mul_zero, norm_zero]
      exact mul_nonneg (div_nonneg (hM₀ θ) Real.two_pi_pos.le) (norm_nonneg _)
    · have hk : circleMap 0 1 θ ∈ K :=
        ⟨diskAnglePoint θ, subset_closure (show diskAnglePoint θ ∈ Function.support P from hp), rfl⟩
      have hPos : 0 ≤ A - (L (cayleyToUpperHalfPlane (circleMap 0 r θ))).re :=
        sub_nonneg.mpr (hBound _ (im_cayleyToUpperHalfPlane_pos (mem_ball_zero_iff.mp (hBall hr.1 hr.2 θ))))
      rw [norm_mul, Real.norm_of_nonneg (div_nonneg hPos Real.two_pi_pos.le)]
      exact mul_le_mul (div_le_div_of_nonneg_right (hθ hk) Real.two_pi_pos.le)
        (P.norm_coe_le_norm _) (norm_nonneg _) (div_nonneg (hM₀ θ) Real.two_pi_pos.le)
  · exact (hM.div_const (2 * Real.pi)).mul_const ‖P‖
  · filter_upwards [hLim] with θ hθ
    exact ((tendsto_const_nhds.sub hθ).div_const (2 * Real.pi)).mul_const (P (diskAnglePoint θ))

/-- The real part of the logarithmic remainder is determined by the
actual boundary logarithm and a nonnegative mass at infinity. -/
theorem exists_blaschkeBoundaryLog_poisson_representation {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, 0 < (a i).im) (hFin : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hSum : Summable (fun i => upperHalfPlaneBlaschkeWeight (a i)))
    {H L : ℂ → ℂ} (hH : Differentiable ℂ H) (hH₀ : ∃ z, H z ≠ 0)
    (hFactor : EqOn H (fun z => upperHalfPlaneBlaschkeProduct a z * Complex.exp (L z))
      {z : ℂ | 0 < z.im})
    {A : ℝ} (hBound : ∀ z : ℂ, 0 < z.im → (L z).re ≤ A)
    (hL : DifferentiableOn ℂ L {z : ℂ | 0 < z.im}) :
    let D (θ : ℝ) := A - Real.log ‖H (cayleyToUpperHalfPlane (circleMap 0 1 θ))‖
    Integrable D diskAngleMeasure ∧ ∃ b : ℝ, 0 ≤ b ∧ ∀ w ∈ ball (0 : ℂ) 1,
      A - (L (cayleyToUpperHalfPlane w)).re =
        (∫ θ, (D θ / (2 * Real.pi)) * diskBoundaryPoissonKernel w (diskAnglePoint θ) ∂diskAngleMeasure) +
        b * (cayleyToUpperHalfPlane w).im := by
  let F (w : ℂ) := (A : ℂ) - L (cayleyToUpperHalfPlane w)
  let D (θ : ℝ) := A - Real.log ‖H (cayleyToUpperHalfPlane (circleMap 0 1 θ))‖
  have hMaps : MapsTo cayleyToUpperHalfPlane (ball 0 1) {z : ℂ | 0 < z.im} :=
    fun _ hw => im_cayleyToUpperHalfPlane_pos (mem_ball_zero_iff.mp hw)
  have hF : DifferentiableOn ℂ F (ball 0 1) :=
    (differentiableOn_const (A : ℂ)).sub (hL.comp differentiableOn_cayleyToUpperHalfPlane hMaps)
  have hFPos (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : 0 ≤ (F w).re := by
    simpa only [F, Complex.sub_re, Complex.ofReal_re] using sub_nonneg.mpr (hBound _ (hMaps hw))
  have hLim := ae_tendsto_re_blaschkeBoundaryLog_radial ha hFin hSum hH hH₀ hFactor
  have hFLim : ∀ᵐ θ ∂diskAngleMeasure, Tendsto (fun r : ℝ => (F (circleMap 0 r θ)).re)
      (𝓝[<] (1 : ℝ)) (𝓝 (D θ)) := by
    filter_upwards [hLim] with θ hθ
    simpa only [F, D, Complex.sub_re, Complex.ofReal_re] using tendsto_const_nhds.sub hθ
  have hD := integrable_diskAngleMeasure_of_radial_re_limit hF hFPos hFLim
  obtain ⟨b, hb, hRep⟩ := exists_diskBoundaryPoissonMeasure_density_add_atom hF hFPos diskCayleyInfinity hD
    fun P hP => by
      simpa only [F, D, Complex.sub_re, Complex.ofReal_re] using
        tendsto_integral_blaschkeBoundaryLog_test ha hFin hSum hH hFactor hBound hL hLim P hP
  refine ⟨hD, b, hb, fun w hw => ?_⟩
  have hKernel : diskBoundaryPoissonKernel w diskCayleyInfinity = (cayleyToUpperHalfPlane w).im := by
    simp only [diskBoundaryPoissonKernel, diskCayleyInfinity, herglotzRieszKernel_def, sub_zero]
    rw [cayleyToUpperHalfPlane, mul_div_assoc, Complex.mul_im]
    simp
  simpa only [F, Complex.sub_re, Complex.ofReal_re, hKernel] using hRep w hw

/-- The boundary density and nonnegative contribution at infinity
for the logarithmic remainder of the actual heated transform. -/
theorem eventually_edgeNormalizedHeat_blaschke_hasBoundaryPoissonRepresentation
    {f : ℝ → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 ≤ b)
    (hEdge : ∀ c > b, ∃ ξ ∈ Ioo b c, 𝓕 (fun x : ℝ => (f x : ℂ)) ξ ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let H := edgeNormalizedHeatFourierLaplace t f b
      let B := upperHalfPlaneBlaschkeProduct (upperHalfPlaneZeroAtIndex H)
      let U : Set ℂ := {z : ℂ | 0 < z.im}
      let A := Real.log (1 + ∫ ξ : ℝ, ‖(𝓕 (fun x : ℝ => (realGaussianSmoothing t f x : ℂ))) ξ‖)
      let D (θ : ℝ) := A - Real.log ‖H (cayleyToUpperHalfPlane (circleMap 0 1 θ))‖
      Summable (fun i : UpperHalfPlaneZeroIndex H =>
        upperHalfPlaneBlaschkeWeight (upperHalfPlaneZeroAtIndex H i)) ∧
      (∀ R : ℝ, {i : UpperHalfPlaneZeroIndex H | ‖upperHalfPlaneZeroAtIndex H i‖ ≤ R}.Finite) ∧
      Integrable D diskAngleMeasure ∧
      ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L U ∧ EqOn H (fun z => B z * Complex.exp (L z)) U ∧
        ∃ c : ℝ, 0 ≤ c ∧ ∀ w ∈ ball (0 : ℂ) 1,
          A - (L (cayleyToUpperHalfPlane w)).re =
          (∫ θ, (D θ / (2 * Real.pi)) * diskBoundaryPoissonKernel w (diskAnglePoint θ) ∂diskAngleMeasure) +
            c * (cayleyToUpperHalfPlane w).im := by
  obtain ⟨y, _, hNonzero⟩ := exists_height_eventually_summable_edgeNormalizedHeat_weightedZeroOrder hf hb hEdge
  have hTime : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hTime, hNonzero, eventually_edgeNormalizedHeat_blaschke_factorization_re_le hf hb hEdge]
    with t ht hN hF
  obtain ⟨hSum, hFin, L, hL, hEq, hBound⟩ := hF
  have hH₀ : ∃ z, edgeNormalizedHeatFourierLaplace t f b z ≠ 0 := ⟨(y : ℂ) * Complex.I, hN.1⟩
  have hEntire := differentiable_edgeNormalizedHeatFourierLaplace hf ht b
  obtain ⟨hInt, hRep⟩ := exists_blaschkeBoundaryLog_poisson_representation
    (fun i => i.1.2) hFin hSum hEntire hH₀ hEq hBound hL.differentiableOn
  exact ⟨hSum, hFin, hInt, L, hL, hEq, hRep⟩

end
end MeyerGeneralProblem
