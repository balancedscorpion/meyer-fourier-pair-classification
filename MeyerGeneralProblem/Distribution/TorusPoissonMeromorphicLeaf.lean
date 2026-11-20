module

public import MeyerGeneralProblem.Distribution.SupportCauchyIntegral
public import MeyerGeneralProblem.Distribution.TorusPoissonLeaf
public import Mathlib.Analysis.Meromorphic.Order

@[expose] public section

/-!
# Meromorphic continuation of the normalized Poisson leaves

A support gap makes the Cauchy integral holomorphic across the real
line. At a support site, separating its unit atom gives a simple
pole with residue `i / (2π)` and an analytic remainder.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Metric ProbabilityTheory Set UnitAddTorus
open scoped NNReal Topology

private theorem supportCauchyIntegral_localDifferentiation
    (η : Measure ℝ) (hP : Integrable (cauchyPDFReal 0 1) η) (z : ℂ)
    {δ : ℝ} (hδ : 0 < δ) (hGap : ∀ᵐ x ∂η, δ ≤ ‖((x : ℝ) : ℂ) - z‖) :
    (∀ w ∈ ball z (δ / 2), Integrable (supportCauchyKernel w) η) ∧
      ∀ w ∈ ball z (δ / 2), Integrable (supportCauchyDerivative w) η ∧
        HasDerivAt (fun v => ∫ x, supportCauchyKernel v x ∂η)
          (∫ x, supportCauchyDerivative w x ∂η) w := by
  let r := δ / 2
  let R := ‖z‖ + r
  let B := 1 + (1 + R) / r
  have hr : 0 < r := half_pos hδ
  have hR : 0 ≤ R := add_nonneg (norm_nonneg _) hr.le
  have hB : 0 ≤ B := by
    unfold B
    exact add_nonneg zero_le_one (div_nonneg (add_nonneg zero_le_one hR) hr.le)
  have hNear (x : ℝ) (hx : δ ≤ ‖(x : ℂ) - z‖) (w : ℂ) (hw : w ∈ ball z r) :
      (x : ℂ) - w ≠ 0 ∧ ‖broadCauchyKernel 1 w x‖ * (1 + |x|) ≤ B := by
    have hw' : ‖w - z‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
    have hTri := norm_add_le ((x : ℂ) - w) (w - z)
    rw [show (x : ℂ) - w + (w - z) = (x : ℂ) - z by ring] at hTri
    have hD : r ≤ ‖(x : ℂ) - w‖ := by
      dsimp only [r] at hw' ⊢
      linarith only [hx, hw', hTri]
    have hW : ‖w‖ ≤ R := by
      have h := norm_sub_norm_le w z
      dsimp only [R]
      linarith only [h, hw']
    exact ⟨norm_pos_iff.mp (hr.trans_le hD), norm_broadCauchyKernel_one_mul_weight_le_of_gap w x hr hD hW⟩
  have hI (x : ℝ) : ‖broadCauchyKernel 1 Complex.I x‖ * (1 + |x|) ≤ 3 := by
    have hIm := Complex.abs_im_le_norm ((x : ℂ) - Complex.I)
    have hD : 1 ≤ ‖(x : ℂ) - Complex.I‖ := by
      simpa only [Complex.sub_im, Complex.ofReal_im, Complex.I_im, zero_sub, abs_neg, abs_one] using hIm
    have h := norm_broadCauchyKernel_one_mul_weight_le_of_gap Complex.I x one_pos hD Complex.norm_I.le
    exact h.trans (by norm_num)
  have hInt (w : ℂ) (hw : w ∈ ball z r) : Integrable (supportCauchyKernel w) η := by
    let C := ‖supportCauchyConstant‖ * ‖w - Complex.I‖ * B * 3
    have hC : 0 ≤ C := by positivity
    refine (hP.const_mul (C * Real.pi)).mono' (measurable_supportCauchyKernel w).aestronglyMeasurable ?_
    filter_upwards [hGap] with x hx
    apply le_mul_poisson_one_of_weight_bound x hC
    rw [supportCauchyKernel_eq_subtraction_product w x (hNear x hx w hw).1, norm_mul, norm_mul, norm_mul]
    calc
      _ = ‖supportCauchyConstant‖ * ‖w - Complex.I‖ *
        (‖broadCauchyKernel 1 w x‖ * (1 + |x|)) *
        (‖broadCauchyKernel 1 Complex.I x‖ * (1 + |x|)) := by ring
      _ ≤ C := by
        unfold C
        gcongr
        · exact (hNear x hx w hw).2
        · exact hI x
  refine ⟨hInt, ?_⟩
  intro w hw
  let C := ‖supportCauchyConstant‖ * B ^ 2
  have hC : 0 ≤ C := by positivity
  have hMeas : AEStronglyMeasurable (supportCauchyDerivative w) η := by
    apply Measurable.aestronglyMeasurable
    unfold supportCauchyDerivative broadCauchyKernel
    fun_prop
  have hDom : ∀ᵐ x ∂η, ∀ v ∈ ball z r,
      ‖supportCauchyDerivative v x‖ ≤ (C * Real.pi) * cauchyPDFReal 0 1 x := by
    filter_upwards [hGap] with x hx v hv
    apply le_mul_poisson_one_of_weight_bound x hC
    calc
      _ = ‖supportCauchyConstant‖ * (‖broadCauchyKernel 1 v x‖ * (1 + |x|)) ^ 2 := by
        simp only [supportCauchyDerivative, norm_mul, broadCauchyKernel, pow_one, norm_pow]
        ring
      _ ≤ C := by
        unfold C
        gcongr
        exact (hNear x hx v hv).2
  have hDeriv : ∀ᵐ x ∂η, ∀ v ∈ ball z r,
      HasDerivAt (fun a => supportCauchyKernel a x) (supportCauchyDerivative v x) v := by
    filter_upwards [hGap] with x hx v hv
    simpa only [supportCauchyKernel, supportCauchyDerivative, Nat.cast_one, one_mul] using
      ((hasDerivAt_broadCauchyKernel_pole_of_sub_ne_zero 1 v x (hNear x hx v hv).1).sub_const
        (broadCauchyKernel 1 Complex.I x)).const_mul supportCauchyConstant
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := supportCauchyKernel)
    (F' := supportCauchyDerivative) (isOpen_ball.mem_nhds hw)
    (Eventually.of_forall fun v => (measurable_supportCauchyKernel v).aestronglyMeasurable)
    (hInt w hw) hMeas hDom (hP.const_mul (C * Real.pi)) hDeriv)

/-- A support gap makes the normalized Cauchy kernel integrable nearby
and its integral holomorphic at the center of that gap. -/
theorem integrable_and_analytic_supportCauchy_of_gap
    (η : Measure ℝ) (hP : Integrable (cauchyPDFReal 0 1) η) (z : ℂ)
    {δ : ℝ} (hδ : 0 < δ) (hGap : ∀ᵐ x ∂η, δ ≤ ‖((x : ℝ) : ℂ) - z‖) :
    (∀ w ∈ ball z (δ / 2), Integrable (supportCauchyKernel w) η) ∧
      AnalyticAt ℂ (fun w => ∫ x, supportCauchyKernel w x ∂η) z := by
  obtain ⟨hInt, hDeriv⟩ := supportCauchyIntegral_localDifferentiation η hP z hδ hGap
  refine ⟨hInt, ?_⟩
  have hDiff : DifferentiableOn ℂ (fun w => ∫ x, supportCauchyKernel w x ∂η) (ball z (δ / 2)) :=
    fun w hw => (hDeriv w hw).2.differentiableAt.differentiableWithinAt
  exact hDiff.analyticOnNhd isOpen_ball z (mem_ball_self (half_pos hδ))


private theorem ae_mem_dsupport_of_discreteSupportCount (T : TemperedDistribution ℝ ℂ) :
    ∀ᵐ x ∂discreteSupportCount T, x ∈ Distribution.dsupport T :=
  ae_restrict_mem Distribution.isClosed_dsupport.measurableSet

private theorem norm_ofReal_sub_eq_real_dist (x a : ℝ) :
    ‖(x : ℂ) - (a : ℂ)‖ = dist x a := by
  rw [← Complex.ofReal_sub, Complex.norm_real, dist_eq_norm]

private theorem exists_ae_dist_ge_of_notMem_dsupport (T : TemperedDistribution ℝ ℂ)
    {a : ℝ} (ha : a ∉ Distribution.dsupport T) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ᵐ x : ℝ ∂discreteSupportCount T, δ ≤ ‖(x : ℂ) - (a : ℂ)‖) := by
  obtain ⟨δ, hδ, hBall⟩ := Metric.isOpen_iff.mp
    (Distribution.isClosed_dsupport (f := (T : SchwartzMap ℝ ℂ → ℂ))).isOpen_compl a ha
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [ae_mem_dsupport_of_discreteSupportCount T] with x hx
  rw [norm_ofReal_sub_eq_real_dist]
  exact le_of_not_gt fun h => hBall (mem_ball.mpr h) hx

/-- The normalized support Cauchy integral extends analytically across
every real point outside the intrinsic support. -/
theorem integrable_and_analyticAt_integral_supportCauchy_of_notMem_dsupport
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : DistributionSupportedOn S.carrier T)
    {K : ℕ} (hCount : ∀ r, (S.carrier ∩ Ico r (r + 1)).ncard ≤ K)
    {a : ℝ} (ha : a ∉ Distribution.dsupport T) :
    Integrable (supportCauchyKernel (a : ℂ)) (discreteSupportCount T) ∧
      AnalyticAt ℂ (fun w => ∫ x, supportCauchyKernel w x ∂discreteSupportCount T) (a : ℂ) := by
  obtain ⟨δ, hδ, hGap⟩ := exists_ae_dist_ge_of_notMem_dsupport T ha
  obtain ⟨hInt, hAnalytic⟩ := integrable_and_analytic_supportCauchy_of_gap _
    (integrable_poisson_discreteSupportCount S T hT hCount 0 (γ := 1) one_pos)
    (a : ℂ) hδ hGap
  exact ⟨hInt _ (mem_ball_self (half_pos hδ)), hAnalytic⟩

/-- At each intrinsic support site the normalized support Cauchy integral
has an analytic remainder after subtracting its simple pole, with residue
`i / (2π)`. -/
theorem exists_supportCauchy_analytic_remainder_at_site
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : DistributionSupportedOn S.carrier T)
    {K : ℕ} (hCount : ∀ r, (S.carrier ∩ Ico r (r + 1)).ncard ≤ K)
    {a : ℝ} (ha : a ∈ Distribution.dsupport T) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (a : ℂ) ∧
      (fun w => ∫ x, supportCauchyKernel w x ∂discreteSupportCount T) =ᶠ[𝓝 (a : ℂ)]
        fun w => -supportCauchyConstant * (w - (a : ℂ))⁻¹ + F w := by
  let η := discreteSupportCount T
  let η₀ := η.restrict ({a}ᶜ : Set ℝ)
  let p : S.subtype := ⟨a, dsupport_subset_of_discrete_support S T hT ha⟩
  let δ := S.isolationRadius p
  have hδ : 0 < δ := S.isolationRadius_pos p
  have hP : Integrable (cauchyPDFReal 0 1) η₀ :=
    (integrable_poisson_discreteSupportCount S T hT hCount 0 (γ := 1) one_pos).integrableOn
  have hGap : ∀ᵐ x ∂η₀, δ ≤ ‖((x : ℝ) : ℂ) - (a : ℂ)‖ := by
    filter_upwards [ae_restrict_of_ae (ae_mem_dsupport_of_discreteSupportCount T),
      ae_restrict_mem (μ := η) (measurableSet_singleton a).compl] with x hx hxa
    rw [norm_ofReal_sub_eq_real_dist]
    exact S.isolationRadius_le_dist p (dsupport_subset_of_discrete_support S T hT hx)
      (by simpa only [mem_compl_iff, mem_singleton_iff] using hxa)
  obtain ⟨hInt, hAnalytic⟩ := integrable_and_analytic_supportCauchy_of_gap η₀ hP (a : ℂ) hδ hGap
  let F (w : ℂ) := (∫ x, supportCauchyKernel w x ∂η₀) -
    supportCauchyConstant * broadCauchyKernel 1 Complex.I a
  have hA : AnalyticAt ℂ F (a : ℂ) := hAnalytic.sub analyticAt_const
  have hMass : η {a} = 1 := by
    change discreteSupportCount T {a} = 1
    rw [discreteSupportCount, Measure.restrict_apply (measurableSet_singleton a), singleton_inter_of_mem ha]
    simp
  have hSplit : η = Measure.dirac a + η₀ := by
    have h := η.restrict_add_restrict_compl (measurableSet_singleton a)
    rw [Measure.restrict_singleton, hMass, one_smul] at h
    exact h.symm
  refine ⟨F, hA, ?_⟩
  filter_upwards [ball_mem_nhds (a : ℂ) (half_pos hδ)] with w hw
  change (∫ x, supportCauchyKernel w x ∂η) = -supportCauchyConstant * (w - (a : ℂ))⁻¹ + F w
  have hD : Integrable (supportCauchyKernel w) (Measure.dirac a) := integrable_dirac (by simp)
  rw [hSplit, integral_add_measure hD (hInt w hw), integral_dirac]
  simp only [F, supportCauchyKernel, broadCauchyKernel, pow_one]
  rw [show (a : ℂ) - w = -(w - (a : ℂ)) by ring, inv_neg]
  ring


/-- The scalar coefficient of each pole is exactly `i / (2π)`. -/
theorem neg_supportCauchyConstant_eq_residue :
    -supportCauchyConstant = Complex.I / (2 * (Real.pi : ℂ)) := by
  rw [supportCauchyConstant, mul_neg, neg_neg, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_ofNat, div_eq_mul_inv, mul_comm]

private theorem supportCauchyConstant_ne_zero : supportCauchyConstant ≠ 0 := by
  unfold supportCauchyConstant
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero Real.two_pi_pos.ne'))
    (neg_ne_zero.mpr Complex.I_ne_zero)

/-- Adding any scalar normalization retains a simple pole with the exact
residue at each support site. -/
theorem meromorphicOrderAt_add_integral_supportCauchy_at_site
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : DistributionSupportedOn S.carrier T)
    {K : ℕ} (hCount : ∀ r, (S.carrier ∩ Ico r (r + 1)).ncard ≤ K)
    (c : ℂ) {a : ℝ} (ha : a ∈ Distribution.dsupport T) :
    let f (w : ℂ) := c + ∫ x, supportCauchyKernel w x ∂discreteSupportCount T
    MeromorphicAt f (a : ℂ) ∧ meromorphicOrderAt f (a : ℂ) = (-1 : ℤ) ∧
      Tendsto (fun w => (w - (a : ℂ)) * f w) (𝓝[≠] (a : ℂ))
        (𝓝 (Complex.I / (2 * (Real.pi : ℂ)))) := by
  let f (w : ℂ) := c + ∫ x, supportCauchyKernel w x ∂discreteSupportCount T
  obtain ⟨F, hF, hExact⟩ := exists_supportCauchy_analytic_remainder_at_site S T hT hCount ha
  let A (w : ℂ) := c + F w
  let P (w : ℂ) := -supportCauchyConstant * (w - (a : ℂ))⁻¹
  have hA : AnalyticAt ℂ A (a : ℂ) := analyticAt_const.add hF
  have hP : MeromorphicAt P (a : ℂ) := by unfold P; fun_prop
  have hEq : f =ᶠ[𝓝[≠] (a : ℂ)] fun w => P w + A w := by
    filter_upwards [hExact.filter_mono nhdsWithin_le_nhds] with w hw
    change c + (∫ x, supportCauchyKernel w x ∂discreteSupportCount T) = _
    rw [hw]
    simp only [P, A]
    abel
  have hMer : MeromorphicAt f (a : ℂ) := (hP.add hA.meromorphicAt).congr hEq.symm
  let g (w : ℂ) := -supportCauchyConstant + (w - (a : ℂ)) * A w
  have hLin : AnalyticAt ℂ (fun w : ℂ => w - (a : ℂ)) (a : ℂ) := analyticAt_id.sub analyticAt_const
  have hg : AnalyticAt ℂ g (a : ℂ) := analyticAt_const.add (hLin.mul hA)
  have hg0 : g (a : ℂ) = -supportCauchyConstant := by simp [g]
  have hgN : g (a : ℂ) ≠ 0 := by rw [hg0, neg_ne_zero]; exact supportCauchyConstant_ne_zero
  have hOrder : meromorphicOrderAt f (a : ℂ) = (-1 : ℤ) := by
    refine (meromorphicOrderAt_eq_int_iff hMer).mpr ⟨g, hg, hgN, ?_⟩
    filter_upwards [hEq, self_mem_nhdsWithin] with w hw he
    have hne : w - (a : ℂ) ≠ 0 := sub_ne_zero.mpr he
    rw [hw, zpow_neg_one, smul_eq_mul]
    simp only [P, g, mul_add, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    ring
  refine ⟨hMer, hOrder, ?_⟩
  rw [← neg_supportCauchyConstant_eq_residue, ← hg0]
  have hLim := hg.continuousAt.tendsto.mono_left
    (show 𝓝[≠] (a : ℂ) ≤ 𝓝 (a : ℂ) from nhdsWithin_le_nhds)
  apply hLim.congr'
  filter_upwards [hEq, self_mem_nhdsWithin] with w hw he
  have hne : w - (a : ℂ) ≠ 0 := sub_ne_zero.mpr he
  change g w = (w - (a : ℂ)) * f w
  rw [hw]
  simp only [g, P, mul_add]
  have hCancel : (w - (a : ℂ)) * (-supportCauchyConstant * (w - (a : ℂ))⁻¹) =
      -supportCauchyConstant := by
    rw [mul_left_comm, mul_inv_cancel₀ hne, mul_one]
  rw [hCancel]

/-- The normalized scalar Cauchy continuation is analytic off its real
support sites, independently of its additive normalization. -/
theorem analyticAt_add_integral_supportCauchy_of_not_mem
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : DistributionSupportedOn S.carrier T)
    {K : ℕ} (hCount : ∀ r, (S.carrier ∩ Ico r (r + 1)).ncard ≤ K)
    (c z : ℂ) (hz : z ∉ Complex.ofReal '' Distribution.dsupport T) :
    AnalyticAt ℂ (fun w => c + ∫ x, supportCauchyKernel w x ∂discreteSupportCount T) z := by
  by_cases h : z.im = 0
  · have hReal : (z.re : ℂ) = z := by apply Complex.ext <;> simp [h]
    have hA : z.re ∉ Distribution.dsupport T := fun ha => hz ⟨z.re, ha, hReal⟩
    rw [← hReal]
    exact analyticAt_const.add (integrable_and_analyticAt_integral_supportCauchy_of_notMem_dsupport S T hT hCount hA).2
  · have hOpen : IsOpen {w : ℂ | w.im ≠ 0} :=
      isOpen_ne_fun Complex.continuous_im continuous_const
    have hDiff : DifferentiableOn ℂ (fun w => c + ∫ x, supportCauchyKernel w x ∂discreteSupportCount T)
        {w : ℂ | w.im ≠ 0} := by
      intro w hw
      exact ((hasDerivAt_integral_supportCauchyKernel_discreteSupportCount S T hT hCount w hw).const_add
        c).differentiableAt.differentiableWithinAt
    exact hDiff.analyticOnNhd hOpen z h


private theorem re_supportCauchyKernel_real (a x : ℝ) :
    (supportCauchyKernel (a : ℂ) x).re = -(cauchyPDFReal 0 1 x) / 2 := by
  simpa only [Complex.ofReal_re, Complex.ofReal_im, Real.toNNReal_zero,
    cauchyPDFReal_scale_zero, Pi.zero_apply, zero_sub] using
    re_supportCauchyKernel_of_im_nonneg (a : ℂ) (by simp) x

/-- Use normalized Haar measure on each circle factor of the phase torus. -/
local instance poissonMeromorphicCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

section MeromorphicPhaseLeaves

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)

/-- The actual normalized Poisson leaf is meromorphic on the complex plane. -/
theorem meromorphic_torusPositivePoissonLeaf (θ : UnitAddTorus d) :
    Meromorphic (torusPositivePoissonLeaf β S T hT hCont hCount θ) := by
  intro z
  by_cases hz : z ∈ Complex.ofReal '' Distribution.dsupport (T θ)
  · obtain ⟨a, ha, rfl⟩ := hz
    exact (meromorphicOrderAt_add_integral_supportCauchy_at_site (S θ) (T θ) (hT θ) (hCount θ)
      (torusPositivePoissonField β S T hT hCont hCount Complex.I θ) ha).1
  · exact (analyticAt_add_integral_supportCauchy_of_not_mem (S θ) (T θ) (hT θ) (hCount θ)
      (torusPositivePoissonField β S T hT hCont hCount Complex.I θ) z hz).meromorphicAt

/-- The poles of the actual normalized phase leaf are exactly the intrinsic
support sites. Each has order `-1` and residue `i / (2π)`. -/
theorem torusPositivePoissonLeaf_poles_and_residues (θ : UnitAddTorus d) :
    (∀ z ∉ Complex.ofReal '' Distribution.dsupport (T θ),
      AnalyticAt ℂ (torusPositivePoissonLeaf β S T hT hCont hCount θ) z) ∧
    ∀ a : ℝ, a ∈ Distribution.dsupport (T θ) →
      meromorphicOrderAt (torusPositivePoissonLeaf β S T hT hCont hCount θ) (a : ℂ) = (-1 : ℤ) ∧
      Tendsto (fun w => (w - (a : ℂ)) * torusPositivePoissonLeaf β S T hT hCont hCount θ w)
        (𝓝[≠] (a : ℂ)) (𝓝 (Complex.I / (2 * (Real.pi : ℂ)))) := by
  let c := torusPositivePoissonField β S T hT hCont hCount Complex.I θ
  exact ⟨analyticAt_add_integral_supportCauchy_of_not_mem (S θ) (T θ) (hT θ) (hCount θ) c,
    fun _ ha => (meromorphicOrderAt_add_integral_supportCauchy_at_site
      (S θ) (T θ) (hT θ) (hCount θ) c ha).2⟩

/-- On a common full-measure set of phases the scalar leaf has zero real
part at every real nonpole. -/
theorem ae_re_torusPositivePoissonLeaf_real_of_notMem_dsupport
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ)) :
    ∀ᵐ θ ∂volume, ∀ a : ℝ, a ∉ Distribution.dsupport (T θ) →
      (torusPositivePoissonLeaf β S T hT hCont hCount θ (a : ℂ)).re = 0 := by
  filter_upwards [ae_re_torusL2PhaseAdvance_supportPositivePoisson
    β S T hT hAdvance hCont hCount 0 (y := 1) one_pos] with θ hθ
  have hBase : (torusPositivePoissonField β S T hT hCont hCount Complex.I θ).re =
      (∫ t, cauchyPDFReal 0 1 t ∂discreteSupportCount (T θ)) / 2 := by
    simpa only [torusPositivePoissonField, Complex.I_re, Complex.I_im, Real.toNNReal_one] using hθ
  intro a ha
  have hInt := (integrable_and_analyticAt_integral_supportCauchy_of_notMem_dsupport
    (S θ) (T θ) (hT θ) (hCount θ) ha).1
  rw [torusPositivePoissonLeaf, Complex.add_re, hBase]
  change _ + Complex.reCLM (∫ x, supportCauchyKernel (a : ℂ) x ∂discreteSupportCount (T θ)) = _
  rw [← Complex.reCLM.integral_comp_comm hInt]
  change _ + (∫ x, (supportCauchyKernel (a : ℂ) x).re ∂discreteSupportCount (T θ)) = _
  simp_rw [re_supportCauchyKernel_real]
  rw [integral_div, integral_neg]
  ring


/-- At a real nonpole the imaginary part of the normalized Poisson leaf
has derivative given by the negative squared-distance integral. -/
theorem hasDerivAt_im_torusPositivePoissonLeaf_of_notMem_dsupport (θ : UnitAddTorus d)
    {a : ℝ} (ha : a ∉ Distribution.dsupport (T θ)) :
    HasDerivAt (fun x : ℝ => (torusPositivePoissonLeaf β S T hT hCont hCount θ (x : ℂ)).im)
      (-(2 * Real.pi)⁻¹ * ∫ x, (x - a)⁻¹ ^ 2 ∂discreteSupportCount (T θ)) a := by
  let η := discreteSupportCount (T θ)
  obtain ⟨δ, hδ, hGap⟩ := exists_ae_dist_ge_of_notMem_dsupport (T θ) ha
  obtain ⟨_, hDeriv⟩ := supportCauchyIntegral_localDifferentiation η
    (integrable_poisson_discreteSupportCount (S θ) (T θ) (hT θ) (hCount θ) 0 (γ := 1) one_pos)
    (a : ℂ) hδ hGap
  obtain ⟨hInt, hAt⟩ := hDeriv (a : ℂ) (mem_ball_self (half_pos hδ))
  have hLeaf := ((hAt.const_add
    (torusPositivePoissonField β S T hT hCont hCount Complex.I θ)).comp_ofReal)
  have hIm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt a hLeaf
  change HasDerivAt (fun x : ℝ => (torusPositivePoissonLeaf β S T hT hCont hCount θ (x : ℂ)).im)
    (Complex.imCLM (∫ x, supportCauchyDerivative (a : ℂ) x ∂η)) a at hIm
  rw [← Complex.imCLM.integral_comp_comm hInt] at hIm
  have hKernel (x : ℝ) :
      Complex.imCLM (supportCauchyDerivative (a : ℂ) x) = -(2 * Real.pi)⁻¹ * (x - a)⁻¹ ^ 2 := by
    have hReal : ((x : ℂ) - (a : ℂ))⁻¹ ^ 2 = (((x - a)⁻¹ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    simp only [Complex.imCLM_apply, supportCauchyDerivative, broadCauchyKernel, hReal,
      supportCauchyConstant, Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
      Complex.neg_im, Complex.I_im, Complex.I_re, mul_zero, zero_mul, add_zero,
      zero_add, mul_neg, one_mul, mul_one, neg_mul, mul_comm]
  have hEq : (∫ x, Complex.imCLM (supportCauchyDerivative (a : ℂ) x) ∂η) =
      -(2 * Real.pi)⁻¹ * ∫ x, (x - a)⁻¹ ^ 2 ∂η := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ hKernel)
  rw [hEq] at hIm
  exact hIm

/-- In particular the normalized leaf's imaginary part is nonincreasing
to first order at every real nonpole, including empty leaves. -/
theorem deriv_im_torusPositivePoissonLeaf_nonpos (θ : UnitAddTorus d)
    {a : ℝ} (ha : a ∉ Distribution.dsupport (T θ)) :
    deriv (fun x : ℝ => (torusPositivePoissonLeaf β S T hT hCont hCount θ (x : ℂ)).im) a ≤ 0 := by
  rw [(hasDerivAt_im_torusPositivePoissonLeaf_of_notMem_dsupport β S T hT hCont hCount θ ha).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity))
    (integral_nonneg fun _ => sq_nonneg _)

end MeromorphicPhaseLeaves

end
end MeyerGeneralProblem
