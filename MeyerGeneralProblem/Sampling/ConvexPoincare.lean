module

public import MeyerGeneralProblem.Sampling.DirichletPoincare
public import MeyerGeneralProblem.Sampling.ClassicalFourierSobolev
public import MeyerGeneralProblem.Carrier.TwoSided
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Order.SuccPred.IntervalSucc

@[expose] public section

/-!
# Convex spectral consequences of the sharp zero-gap inequality

The interval sum retains the actual two-sided coverage and exact pi constant.
The convex lift is the supporting-line argument of KNS Lemma 3; weighted
integrability is explicit and cannot be replaced by a default Bochner integral.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter Function
open scoped Topology Interval FourierTransform

/-- The genuine consecutive intervals of a two-sided carrier cover the line. -/
theorem TwoSidedCarrier.iUnion_gapIntervals (Λ : TwoSidedCarrier) :
    (⋃ j : ℤ, Ioc (Λ j) (Λ (j+1))) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨lo, hlo⟩ := (Λ.tendsto_atBot.eventually (eventually_lt_atBot x)).exists
  obtain ⟨hi, hhi⟩ := (Λ.tendsto_atTop.eventually (eventually_ge_atTop x)).exists
  have hx : x ∈ Ioc (Λ.point lo) (Λ.point hi) := ⟨hlo,hhi⟩
  rw [← Λ.strictMono.monotone.biUnion_Ico_Ioc_map_succ lo hi] at hx
  simp only [mem_iUnion] at hx ⊢
  obtain ⟨j, _, hj⟩ := hx
  exact ⟨j, by simpa using hj⟩

/-- Integrable functions sum over the actual disjoint consecutive gaps. -/
theorem TwoSidedCarrier.hasSum_gapIntegrals (Λ : TwoSidedCarrier)
    (g : ℝ → ℝ) (hg : Integrable g) :
    HasSum (fun j : ℤ => ∫ x in Ioc (Λ j) (Λ (j+1)), g x) (∫ x, g x) := by
  have hd : Pairwise (Disjoint on (fun j : ℤ => Ioc (Λ j) (Λ (j+1)))) := by
    simpa using Λ.strictMono.monotone.pairwise_disjoint_on_Ioc_succ
  have hu := Λ.iUnion_gapIntervals
  have h := hasSum_integral_iUnion (fun j : ℤ =>
    (measurableSet_Ioc : MeasurableSet (Ioc (Λ j) (Λ (j+1))))) hd
      hg.integrableOn
  simpa only [hu, Measure.restrict_univ] using h

/-- Only gaps on which the function is nonzero need the length bound.
This retains actual two-sided coverage while allowing arbitrary inactive
central gaps for a genuinely tail-supported localizer. -/
theorem complex_poincare_of_active_twoSided_zeros (Λ : TwoSidedCarrier) {L : ℝ}
    (hL : 0 ≤ L)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hzero : ∀ j : ℤ, f (Λ j) = 0)
    (hgap : ∀ j : ℤ, (∃ x ∈ Ioc (Λ j) (Λ (j+1)), f x ≠ 0) → Λ (j+1)-Λ j ≤ L)
    (hF : Integrable (fun x => ‖f x‖^2))
    (hD : Integrable (fun x => ‖deriv f x‖^2)) :
    Real.pi^2*(∫ x, ‖f x‖^2) ≤ L^2*(∫ x, ‖deriv f x‖^2) := by
  apply hasSum_le (g := fun j : ℤ => L^2*(∫ x in Ioc (Λ j) (Λ (j+1)), ‖deriv f x‖^2))
    (f := fun j : ℤ => Real.pi^2*(∫ x in Ioc (Λ j) (Λ (j+1)), ‖f x‖^2)) ?_
    (Λ.hasSum_gapIntegrals _ hF |>.mul_left (Real.pi^2))
    (Λ.hasSum_gapIntegrals _ hD |>.mul_left (L^2))
  intro j
  by_cases ha : ∃ x ∈ Ioc (Λ j) (Λ (j+1)), f x ≠ 0
  swap
  · have hz : (∫ x in Ioc (Λ j) (Λ (j+1)), ‖f x‖^2) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      have hfz : f x = 0 := by by_contra h; exact ha ⟨x,hx,h⟩
      simp [hfz]
    rw [hz, mul_zero]
    exact mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => sq_nonneg _))
  have hj : Λ j < Λ (j+1) := Λ.strictMono (by omega)
  have hp := complex_dirichlet_poincare_wirtinger hj f hf (hzero j) (hzero (j+1))
  rw [intervalIntegral.integral_of_le hj.le,
    intervalIntegral.integral_of_le hj.le] at hp
  have hsq : (Λ (j+1)-Λ j)^2 ≤ L^2 :=
    (sq_le_sq₀ (sub_nonneg.mpr hj.le) hL).mpr (hgap j ha)
  exact hp.trans (mul_le_mul_of_nonneg_right hsq (integral_nonneg (fun _ => sq_nonneg _)))

/-- A globally bounded genuine zero-gap carrier is the special case
where every interval has the same length bound. -/
theorem complex_poincare_of_twoSided_zeros (Λ : TwoSidedCarrier) {L : ℝ}
    (hL : 0 ≤ L) (hgap : ∀ j : ℤ, Λ (j+1)-Λ j ≤ L)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hzero : ∀ j : ℤ, f (Λ j) = 0)
    (hF : Integrable (fun x => ‖f x‖^2))
    (hD : Integrable (fun x => ‖deriv f x‖^2)) :
    Real.pi^2*(∫ x, ‖f x‖^2) ≤ L^2*(∫ x, ‖deriv f x‖^2) :=
  complex_poincare_of_active_twoSided_zeros Λ hL f hf hzero (fun j _ => hgap j) hF hD

/-- A convex differentiable function lies above its genuine tangent line
on the whole nonnegative half-line, on both sides of the tangency point. -/
theorem convex_tangent_le_on_nonnegative {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ)
    {a : ℝ} (ha : 0 ≤ a) (hd : DifferentiableAt ℝ Φ a) {x : ℝ} (hx : 0 ≤ x) :
    Φ a + deriv Φ a*(x-a) ≤ Φ x := by
  rcases lt_trichotomy x a with h | h | h
  · have hs := hΦ.slope_le_deriv hx ha h hd
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith
  · subst x; simp
  · have hs := hΦ.deriv_le_slope ha hx h hd
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith

/-- A second-moment lower bound lifts to any differentiable increasing
convex weight. No probability normalization, nonzero mass, or extra higher
moment is assumed; the displayed weighted integral must actually exist. -/
theorem convex_weighted_integral_of_secondMoment
    (w : ℝ → ℝ) (hw : ∀ x, 0 ≤ w x) (hwi : Integrable w)
    (hxi : Integrable (fun x => x^2*w x))
    {a : ℝ} (ha : 0 < a) (hgap : a*(∫ x, w x) ≤ ∫ x, x^2*w x)
    (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ (Ici 0) Φ) (hmono : MonotoneOn Φ (Ici 0))
    (hd : DifferentiableAt ℝ Φ a) (hΦi : Integrable (fun x => Φ (x^2)*w x)) :
    Φ a*(∫ x, w x) ≤ ∫ x, Φ (x^2)*w x := by
  have hderiv : 0 ≤ deriv Φ a := by
    rw [← derivWithin_of_mem_nhds (Ici_mem_nhds ha)]
    exact hmono.derivWithin_nonneg
  have hlin : Integrable (fun x => Φ a*w x + deriv Φ a*(x^2*w x-a*w x)) :=
    (hwi.const_mul _).add ((hxi.sub (hwi.const_mul _)).const_mul _)
  have hi := integral_mono hlin hΦi (fun x => show
      Φ a*w x + deriv Φ a*(x^2*w x-a*w x) ≤ Φ (x^2)*w x from by
    have h := mul_le_mul_of_nonneg_right
      (convex_tangent_le_on_nonnegative hΦ ha.le hd (sq_nonneg x)) (hw x)
    nlinarith)
  have hsum := integral_add (hwi.const_mul (Φ a))
    ((hxi.sub (hwi.const_mul a)).const_mul (deriv Φ a))
  simp only [Pi.sub_apply] at hsum
  rw [hsum,
    integral_const_mul, integral_const_mul, integral_sub hxi (hwi.const_mul _),
    integral_const_mul] at hi
  nlinarith [mul_nonneg hderiv (sub_nonneg.mpr hgap)]

/-- The actual inverse L2 Fourier representative of a C1 Sobolev function
has its finite second moment, with the exact angular Plancherel factor. -/
theorem inverseFourier_secondMoment_of_classical_deriv
    {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hF : MemLp f 2) (hD : MemLp (deriv f) 2) :
    let G := ((𝓕⁻ hF.toLp : Lp ℂ 2 volume) : ℝ → ℂ)
    Integrable (fun x => x^2*‖G x‖^2) ∧
      (∫ x, ‖deriv f x‖^2) = (2*Real.pi)^2*(∫ x, x^2*‖G x‖^2) := by
  let G := ((𝓕⁻ hF.toLp : Lp ℂ 2 volume) : ℝ → ℂ)
  have hDs (j : ℕ) (hj : j ≤ 1) : MemLp (iteratedDeriv j f) 2 := by
    rcases (show j=0 ∨ j=1 by omega) with rfl | rfl
    · simpa using hF
    · simpa using hD
  obtain ⟨hK, _, hnorm⟩ := memLp_fourierDerivativeData_of_classical_derivatives 1 hf hF hDs
  have he (x : ℝ) : ‖fourierDerivativeData 1 G x‖^2 =
      (2*Real.pi)^2*(x^2*‖G x‖^2) := by
    rw [norm_fourierDerivativeData]
    simp only [pow_one, mul_pow, sq_abs]
    ring
  have hM := integrable_norm_sq_of_memLp_complex hK
  have hefun : (fun x => x^2*‖G x‖^2) =
      fun x => ((2*Real.pi)^2)⁻¹*‖fourierDerivativeData 1 G x‖^2 := by
    funext x
    rw [he]
    field_simp
  have hxi : Integrable (fun x => x^2*‖G x‖^2) := by
    rw [hefun]
    exact hM.const_mul _
  refine ⟨hxi, ?_⟩
  have hnorm' : ‖hK.toLp‖^2 = ∫ x, ‖deriv f x‖^2 := by
    rw [hnorm, ← integral_norm_sq_eq_toLp_norm_sq_complex (hDs 1 le_rfl)]
    simp
  rw [← hnorm', ← integral_norm_sq_eq_toLp_norm_sq_complex hK]
  change (∫ x, ‖fourierDerivativeData 1 G x‖^2) =
    (2*Real.pi)^2*(∫ x, x^2*‖G x‖^2)
  simp_rw [he]
  exact integral_const_mul _ _

/-- KNS's convex spectral zero-gap inequality for an actual C1 Sobolev
function and its genuine inverse L2 Fourier transform. The sharp scale is
1/(2t), and the convex weighted integral has an explicit finiteness premise. -/
theorem convex_poincare_of_active_twoSided_zeros
    (Λ : TwoSidedCarrier) {t : ℝ} (ht : 0 < t)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hzero : ∀ j : ℤ, f (Λ j) = 0)
    (hgap : ∀ j : ℤ, (∃ x ∈ Ioc (Λ j) (Λ (j+1)), f x ≠ 0) →
      Λ (j+1)-Λ j ≤ (2*t)⁻¹)
    (hF : MemLp f 2) (hD : MemLp (deriv f) 2)
    (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ (Ici 0) Φ) (hmono : MonotoneOn Φ (Ici 0))
    (hd : DifferentiableAt ℝ Φ (t^2))
    (hΦi : Integrable (fun x => Φ (x^2)*‖(𝓕⁻ hF.toLp : Lp ℂ 2 volume) x‖^2)) :
    Φ (t^2)*(∫ x, ‖f x‖^2) ≤
      ∫ x, Φ (x^2)*‖(𝓕⁻ hF.toLp : Lp ℂ 2 volume) x‖^2 := by
  let G := ((𝓕⁻ hF.toLp : Lp ℂ 2 volume) : ℝ → ℂ)
  have hG : MemLp G 2 := Lp.memLp _
  have hmass : (∫ x, ‖G x‖^2) = ∫ x, ‖f x‖^2 := by
    rw [integral_norm_sq_eq_toLp_norm_sq_complex hG,
      integral_norm_sq_eq_toLp_norm_sq_complex hF]
    have heq : hG.toLp = (𝓕⁻ hF.toLp : Lp ℂ 2 volume) :=
      Lp.ext hG.coeFn_toLp
    rw [heq, ← Lp.norm_fourier_eq (𝓕⁻ hF.toLp), FourierTransform.fourier_fourierInv_eq]
  obtain ⟨hxi,henergy⟩ := inverseFourier_secondMoment_of_classical_deriv hf hF hD
  have hp := complex_poincare_of_active_twoSided_zeros Λ (by positivity) f hf hzero hgap
    (integrable_norm_sq_of_memLp_complex hF) (integrable_norm_sq_of_memLp_complex hD)
  rw [henergy] at hp
  have hsecond : t^2*(∫ x, ‖G x‖^2) ≤ ∫ x, x^2*‖G x‖^2 := by
    rw [hmass]
    have hmul := mul_le_mul_of_nonneg_left hp (sq_nonneg (2*t))
    have hp0 : Real.pi ≠ 0 := Real.pi_ne_zero
    have ht0 : t ≠ 0 := ht.ne'
    field_simp at hmul
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have h := convex_weighted_integral_of_secondMoment (fun x => ‖G x‖^2)
    (fun _ => sq_nonneg _) (integrable_norm_sq_of_memLp_complex hG) hxi
    (sq_pos_of_pos ht) hsecond Φ hΦ hmono hd hΦi
  rwa [hmass] at h

end

end MeyerGeneralProblem
