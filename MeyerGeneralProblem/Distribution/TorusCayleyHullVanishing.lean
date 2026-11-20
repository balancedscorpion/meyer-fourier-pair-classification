module

public import MeyerGeneralProblem.Distribution.TorusBandRepresentative
public import MeyerGeneralProblem.Distribution.TorusCayleyDampingProduct
public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyCommonBand
public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyPoissonAverage
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-!
# Vanishing of a Cayley finite difference on the hull

The real boundary formula and the entire band representatives give an
identity at every real point on almost every phase leaf. At an atom the
Cayley symbol is one, so the finite difference has order at least q.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Set UnitAddTorus
open scoped ENNReal Topology

local notation "SeqL2(" ι ")" => lp (fun _ : ι => ℂ) 2

/-- Use normalized Haar measure on each circle factor. -/
local instance hullVanishingCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

private theorem analyticAt_realRestriction {f : ℂ → ℂ} {a : ℝ}
    (hf : AnalyticAt ℂ f (a : ℂ)) : AnalyticAt ℝ (fun x : ℝ => f (x : ℂ)) a :=
  hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt a)

private theorem iteratedDeriv_pow_mul_eq_zero_of_analyticAt_zero
    {g h : ℝ → ℂ} {a : ℝ} (hg : AnalyticAt ℝ g a) (hh : AnalyticAt ℝ h a)
    (hZero : g a = 0) (q j : ℕ) (hj : j < q) :
    iteratedDeriv j (fun x => g x ^ q * h x) a = 0 := by
  have h₁ : (1 : ℕ) ≤ analyticOrderAt g a := by
    apply Order.one_le_iff_ne_zero.mpr
    exact hg.analyticOrderAt_ne_zero.mpr hZero
  obtain ⟨g₁, hg₁, hFactor⟩ := (natCast_le_analyticOrderAt hg (n := 1)).mp h₁
  have hp : AnalyticAt ℝ (fun x => g x ^ q * h x) a := (hg.pow q).mul hh
  have hq : (q : ℕ∞) ≤ analyticOrderAt (fun x => g x ^ q * h x) a := by
    apply (natCast_le_analyticOrderAt hp).mpr
    refine ⟨fun x => g₁ x ^ q * h x, (hg₁.pow q).mul hh, ?_⟩
    filter_upwards [hFactor] with x hx
    rw [hx, pow_one]
    simp only [Algebra.smul_def, map_pow, mul_pow, mul_assoc]
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hp).mp hq j hj

private theorem analyticAt_eventuallyEq_of_realRestriction_eq {f g : ℂ → ℂ} (a : ℝ)
    (hf : AnalyticAt ℂ f (a : ℂ)) (hg : AnalyticAt ℂ g (a : ℂ))
    (hEq : ∀ x : ℝ, f (x : ℂ) = g (x : ℂ)) :
    f =ᶠ[𝓝 (a : ℂ)] g := by
  rcases hf.eventually_eq_or_eventually_ne hg with h | h
  · exact h
  · have hT : Tendsto Complex.ofReal (𝓝[≠] a) (𝓝[≠] (a : ℂ)) := by
      apply tendsto_inf.mpr
      refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      apply tendsto_principal.mpr
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact fun he => hx (Complex.ofReal_injective he)
    have hFalse : ∀ᶠ _ : ℝ in 𝓝[≠] a, False :=
      (hT.eventually h).mono fun x hx => hx (hEq x)
    exact (Filter.NeBot.ne (inferInstance : (𝓝[≠] a).NeBot)
      (eventually_false_iff_eq_bot.mp hFalse)).elim

private theorem eqOn_upperHalfPlane_of_realRestriction_eq {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im})
    (hg : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.im})
    (hf₀ : AnalyticAt ℂ f 0) (hg₀ : AnalyticAt ℂ g 0)
    (hEq : ∀ x : ℝ, f (x : ℂ) = g (x : ℂ)) :
    EqOn f g {z : ℂ | 0 ≤ z.im} := by
  have hn : f =ᶠ[𝓝 (0 : ℂ)] g := by
    simpa only [Complex.ofReal_zero] using
      analyticAt_eventuallyEq_of_realRestriction_eq 0 hf₀ hg₀ hEq
  obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhds_iff.mp hn
  let p := (((ε / 2 : ℝ) : ℂ)) * Complex.I
  have hp : p ∈ {z : ℂ | 0 < z.im} := by
    change 0 < (((ε / 2 : ℝ) : ℂ) * Complex.I).im
    simpa [Complex.mul_im] using half_pos hε
  have hpBall : p ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    simpa only [p, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg (half_pos hε).le,
      mul_one] using half_lt_self hε
  have hpNear : ∀ᶠ z in 𝓝 p, z ∈ Metric.ball (0 : ℂ) ε :=
    Metric.isOpen_ball.mem_nhds hpBall
  have hpEq : f =ᶠ[𝓝 p] g := hpNear.mono hBall
  have hUpper := hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_im_gt 0).isPreconnected hp hpEq
  intro z hz
  by_cases hPos : 0 < z.im
  · exact hUpper hPos
  · have hIm : z.im = 0 := le_antisymm (le_of_not_gt hPos) hz
    have he : (z.re : ℂ) = z := by
      apply Complex.ext
      · simp
      · simp [hIm]
    rw [← he]
    exact hEq z.re

section

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

/-- The actual nonzero band finite difference has an entire representative
which vanishes to order at least q at every intrinsic support point on
Haar-almost every phase leaf. -/
theorem exists_entire_torusCayleyFiniteDifference_vanishing_on_hull
    (E W : ℝ)
    (hE : HasSum (fun n : d → ℤ => torusDirectionalFrequency β n *
      ‖mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) n‖ ^ 2) E)
    (q : ℕ) (hWidth : (q : ℝ) * E < W) :
    let e := (mFourierBasis (d := d)).repr
    let U : SeqL2(d → ℤ) →L[ℂ] SeqL2(d → ℤ) :=
      (torusPoissonCayleyConvolution β S T hT hCont hCount hAdvance : _ ≃ₗᵢ[ℂ] _)
    let Ξ := torusPoissonCayleyExtendedLeaf β S T hT hCont hCount
    ∃ (W₀ : ℝ) (f : SeqL2(d → ℤ)) (F G : UnitAddTorus d → ℂ)
      (A R : UnitAddTorus d → ℂ → ℂ),
      0 ≤ W₀ ∧ f ≠ 0 ∧ ((U - 1) ^ q) f ≠ 0 ∧
      (∀ n : d → ℤ, torusDirectionalFrequency β n ∉ Icc 0 W₀ →
        f n = 0 ∧ ((U - 1) ^ q) f n = 0) ∧
      Measurable F ∧ Measurable G ∧ F =ᵐ[volume] e.symm f ∧
      G =ᵐ[volume] e.symm (((U - 1) ^ q) f) ∧
      ∀ᵐ θ ∂volume, Differentiable ℂ (A θ) ∧ Differentiable ℂ (R θ) ∧
        (∀ᵐ x : ℝ ∂volume, A θ (x : ℂ) = F (unitAddTorusFlow β x θ)) ∧
        (∀ᵐ x : ℝ ∂volume, R θ (x : ℂ) = G (unitAddTorusFlow β x θ)) ∧
        (∀ z : ℂ, 0 ≤ z.im → R θ z = (Ξ θ z - 1) ^ q * A θ z) ∧
        ∀ a ∈ Distribution.dsupport (T θ), ∀ j < q,
          iteratedDeriv j (fun x : ℝ => R θ (x : ℂ)) a = 0 := by
  intro e U Ξ
  obtain ⟨W₀, f, hW₀, hf, hR, hBand⟩ :=
    exists_nonzero_torusPoissonCayleyFiniteDifference_in_band β S T hT hCont hCount hAdvance E W hE q hWidth
  let r := ((U - 1) ^ q) f
  have hfBand (n : d → ℤ) (hn : torusDirectionalFrequency β n ∉ Icc 0 W₀) : f n = 0 := by
    have h := (hBand n hn).2 0 (Nat.zero_le q)
    rw [pow_zero] at h
    exact h
  have hrBand (n : d → ℤ) (hn : torusDirectionalFrequency β n ∉ Icc 0 W₀) : r n = 0 :=
    (hBand n hn).1
  have hCoeff (v : SeqL2(d → ℤ)) (n : d → ℤ) : mFourierCoeff (e.symm v) n = v n := by
    rw [← mFourierBasis_repr]
    change e (e.symm v) n = v n
    rw [e.apply_symm_apply]
  obtain ⟨N, k, F, _, _, _, hF, hFRep, hFA⟩ :=
    exists_entire_torusOrbit_representative_of_bounded_band β W₀ (e.symm f)
      (fun n hn => (hCoeff f n).trans (hfBand n hn))
  obtain ⟨N', k', G, _, _, _, hG, hGRep, hGR⟩ :=
    exists_entire_torusOrbit_representative_of_bounded_band β W₀ (e.symm r)
      (fun n hn => (hCoeff r n).trans (hrBand n hn))
  let A (θ : UnitAddTorus d) (z : ℂ) :=
    ∫ t : ℝ, k (z - (t : ℂ)) * F (unitAddTorusFlow β t θ)
  let R (θ : UnitAddTorus d) (z : ℂ) :=
    ∫ t : ℝ, k' (z - (t : ℂ)) * G (unitAddTorusFlow β t θ)
  obtain ⟨Q, hQ, _, hQRep, _⟩ :=
    exists_boundedCayleyBoundary_poisson_field β S T hT hCont hCount hAdvance
  let prod (θ : UnitAddTorus d) := (Q θ - 1) ^ q * F θ
  have hProd : Measurable prod := ((hQ.sub measurable_const).pow_const q).mul hF
  have hSymb : G =ᵐ[volume] prod := by
    filter_upwards [hGRep, hFRep, hQRep,
      ae_repr_symm_torusCayleyFiniteDifference β S T hT hCont hCount hAdvance q f]
      with θ hGθ hFθ hQθ hProdθ
    change G θ = (Q θ - 1) ^ q * F θ
    rw [hGθ, show e.symm r θ = _ from hProdθ, hQθ, hFθ]
  have hProdOrbit := ae_torusOrbit_congr β G prod hG hProd hSymb
  have hQOrbit := ae_ae_boundedCayleyBoundary_phaseAdvance_eq_realLeaf
    β S T hT hCont hCount hAdvance Q hQ hQRep
  have hAnalytic := ae_analyticAt_norm_torusPoissonCayleyExtendedLeaf
    β S T hT hCont hCount hAdvance
  have hAnalyticUpper := ae_analyticOnNhd_norm_torusPoissonCayleyField
    β S T hT hCont hCount hAdvance
  refine ⟨W₀, f, F, G, A, R, hW₀, hf, hR, fun n hn => ⟨hfBand n hn, hrBand n hn⟩,
    hF, hG, hFRep, hGRep, ?_⟩
  filter_upwards [hFA, hGR, hProdOrbit, hQOrbit, hAnalytic, hAnalyticUpper]
    with θ hFAθ hGRθ hProdθ hQθ hAnalyticθ hAnalyticUpperθ
  have hAθ : Differentiable ℂ (A θ) := hFAθ.1
  have hRθ : Differentiable ℂ (R θ) := hGRθ.1
  have hAf : (fun x : ℝ => A θ (x : ℂ)) =ᵐ[volume] fun x => F (unitAddTorusFlow β x θ) :=
    hFAθ.2
  have hRf : (fun x : ℝ => R θ (x : ℂ)) =ᵐ[volume] fun x => G (unitAddTorusFlow β x θ) :=
    hGRθ.2
  have ha : (fun x : ℝ => R θ (x : ℂ)) =ᵐ[volume]
      fun x => (Ξ θ (x : ℂ) - 1) ^ q * A θ (x : ℂ) := by
    filter_upwards [hAf, hRf, hProdθ, hQθ] with x h1 h2 h3 h4
    change G (unitAddTorusFlow β x θ) = (Q (unitAddTorusFlow β x θ) - 1) ^ q *
      F (unitAddTorusFlow β x θ) at h3
    rw [h2, h3, h4, h1]
  have hΞ : Continuous (fun x : ℝ => Ξ θ (x : ℂ)) := continuous_iff_continuousAt.mpr fun x =>
    (hAnalyticθ x).1.continuousAt.comp Complex.continuous_ofReal.continuousAt
  have hAp : Continuous (fun x : ℝ => A θ (x : ℂ)) := hAθ.continuous.comp Complex.continuous_ofReal
  have hRp : Continuous (fun x : ℝ => R θ (x : ℂ)) := hRθ.continuous.comp Complex.continuous_ofReal
  have hEq : (fun x : ℝ => R θ (x : ℂ)) = fun x : ℝ => (Ξ θ (x : ℂ) - 1) ^ q * A θ (x : ℂ) :=
    Measure.eq_of_ae_eq ha hRp (((hΞ.sub continuous_const).pow q).mul hAp)
  let V := {z : ℂ | 0 < z.im}
  have hV : IsOpen V := isOpen_lt continuous_const Complex.continuous_im
  have hXiUpper : AnalyticOnNhd ℂ (Ξ θ) V := by
    intro z hz
    apply (hAnalyticUpperθ.1 z hz).congr
    filter_upwards [hV.mem_nhds hz] with w hw
    exact (torusPoissonCayleyExtendedLeaf_eq_field β S T hT hCont hCount θ hw).symm
  have hXi₀ : AnalyticAt ℂ (Ξ θ) 0 := by simpa only [Complex.ofReal_zero] using (hAnalyticθ 0).1
  have hAct : EqOn (R θ) (fun z => (Ξ θ z - 1) ^ q * A θ z) {z : ℂ | 0 ≤ z.im} :=
    eqOn_upperHalfPlane_of_realRestriction_eq (fun z _ => hRθ.analyticAt z)
      (((hXiUpper.sub analyticOnNhd_const).pow q).mul (fun z _ => hAθ.analyticAt z))
      (hRθ.analyticAt 0) (((hXi₀.sub analyticAt_const).pow q).mul (hAθ.analyticAt 0))
      (fun x => congrFun hEq x)
  refine ⟨hAθ, hRθ, hAf, hRf, hAct, ?_⟩
  intro a ha j hj
  have hZero : Ξ θ (a : ℂ) - 1 = 0 := by
    simp [Ξ, torusPoissonCayleyExtendedLeaf, ha]
  have hAnalyticA : AnalyticAt ℂ (A θ) (a : ℂ) := hAθ.analyticAt (a : ℂ)
  rw [hEq]
  exact iteratedDeriv_pow_mul_eq_zero_of_analyticAt_zero
    ((analyticAt_realRestriction (hAnalyticθ a).1).sub analyticAt_const)
    (analyticAt_realRestriction hAnalyticA) hZero q j hj

end
end
end MeyerGeneralProblem
